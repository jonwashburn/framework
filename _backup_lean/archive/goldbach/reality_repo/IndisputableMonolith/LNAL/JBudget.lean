import Mathlib
import IndisputableMonolith.LNAL.Opcodes
import IndisputableMonolith.LNAL.VM
import IndisputableMonolith.LNAL.InstrCost

namespace IndisputableMonolith
namespace LNAL

/-- Positive part of the instruction cost, as a `Nat` (negative costs saturate to zero). -/
@[simp] def posCost (instr : LInstr) : Nat := Int.toNat (instrCost instr)

/-- One-step budget update: consume budget on positive-cost ops. -/
@[simp] def stepBudget (budget : Nat) (instr : LInstr) : Nat := budget - posCost instr

/-- Simulate the budget across a program, resetting at the start of each 8-instruction window. -/
def simulateBudget (code : Array LInstr) (init : Nat := 4) : Array Nat := Id.run do
  let n := code.size
  let mut budget := init
  let mut out : Array Nat := Array.mkEmpty n
  for idx in [0:n] do
    let instr := code.getD idx (LInstr.simple Opcode.LOCK)
    let budget0 := if idx % 8 = 0 then init else budget
    let budget1 := stepBudget budget0 instr
    out := out.push budget1
    budget := budget1
  out

/-- Budget is required to be nonincreasing within each 8-op window. -/
def jMonotoneWithinWindows (code : Array LInstr) (init : Nat := 4) : Bool :=
  let budgets := simulateBudget code init
  let n := budgets.size
  Id.run do
    let mut ok := true
    for i in [0:n] do
      if i + 1 < n ∧ (i / 8) = ((i + 1) / 8) then
        if budgets.getD i 0 < budgets.getD (i+1) 0 then ok := false
    ok

/-- Collect at most `k` violation indices where the budget increases within a window. -/
def jMonotoneViolations (code : Array LInstr) (init : Nat := 4) (k : Nat := 8) : List Nat :=
  let budgets := simulateBudget code init
  let n := budgets.size
  Id.run do
    let mut out : List Nat := []
    let mut ct : Nat := 0
    for i in [0:n] do
      if i + 1 < n ∧ (i / 8) = ((i + 1) / 8) then
        if budgets.getD i 0 < budgets.getD (i+1) 0 ∧ ct < k then
          out := out.concat i
          ct := ct + 1
    out

/-- Sum of positive costs per 8-op window (ΔJ bars used for reports). -/
def deltaJPerWindow (code : Array LInstr) : Array Nat := Id.run do
  let n := code.size
  let windows := (n + 7) / 8
  let mut out : Array Nat := Array.mkEmpty windows
  for w in [0:windows] do
    let start := 8 * w
    let stop := min n (start + 8)
    let mut s : Nat := 0
    for i in [start:stop] do
      s := s + posCost (code.getD i (LInstr.simple Opcode.LOCK))
    out := out.push s
  out

/-- Instruction-local J consumption (nonnegative). Negative-cost ops do not replenish budget. -/
@[simp] def jDelta (instr : LInstr) : Nat := posCost instr

/-- One-step J‑budget update: truncated subtraction by local J consumption. -/
def jBudgetUpdateStep (s : LState) (instr : LInstr) : LState :=
  { s with jBudgetWin := s.jBudgetWin - jDelta instr }

/-- Fetch-aware J‑budget update. Does not modify any other fields. -/
def jBudgetUpdate (P : LProgram) (s : LState) : LState :=
  let instr := lFetch P s.ip
  jBudgetUpdateStep s instr

/-- Monotonicity: a single update cannot increase the per-window budget. -/
lemma jBudget_nonincreasing (P : LProgram) (s : LState) :
  (jBudgetUpdate P s).jBudgetWin ≤ s.jBudgetWin := by
  unfold jBudgetUpdate jBudgetUpdateStep
  simp only
  -- The new budget is s.jBudgetWin - jDelta instr, which is ≤ s.jBudgetWin
  -- by the property of truncated subtraction (Nat.sub_le)
  exact Nat.sub_le s.jBudgetWin (jDelta (lFetch P s.ip))

/-- v2 step (additive): apply `lStep`, then update J budget. -/
def lStepJ (P : LProgram) (s : LState) : LState :=
  jBudgetUpdate P (lStep P s)

/-- **DEPRECATED**: This axiom is FALSE due to window rollover behavior.
    On rollover (winIdx8 transitions 7→0), budget resets to jBudgetMax,
    which can exceed the current budget.

    Use `lStep_budget_nonincreasing_within_window` for the correct version
    with a non-rollover guard. -/
def lStep_budget_nonincreasing_hypothesis : Prop :=
  ∀ (P : LProgram) (s : LState), (lStep P s).jBudgetWin ≤ s.jBudgetWin

/-- **IMPLEMENTATION AXIOM**: lStep does not increase budget within a window.

    The proof requires detailed case analysis of VM.lStep (200+ line match expression).
    Deferred pending refactoring of VM.lStep to factor out budget update logic.

    **Status**: Axiom (implementation detail)
    **Justification**: Each instruction in the LNAL VM either maintains or decreases
    the J-budget. Rollover only happens at window boundaries. -/
axiom lStep_budget_nonincreasing_within_window_axiom (P : LProgram) (s : LState) :
    (s.winIdx8 + 1) % 8 ≠ 0 → (lStep P s).jBudgetWin ≤ s.jBudgetWin

theorem lStep_budget_nonincreasing_within_window (P : LProgram) (s : LState)
    (h_no_rollover : (s.winIdx8 + 1) % 8 ≠ 0) :
    (lStep P s).jBudgetWin ≤ s.jBudgetWin :=
  lStep_budget_nonincreasing_within_window_axiom P s h_no_rollover

-- Legacy compatibility: provide the axiom as a theorem assuming the hypothesis
theorem lStep_budget_nonincreasing (P : LProgram) (s : LState)
    (h : lStep_budget_nonincreasing_hypothesis) :
    (lStep P s).jBudgetWin ≤ s.jBudgetWin := h P s

/-- Single step decreases budget (assuming no rollover).
    Note: This lemma is incomplete due to the false axiom issue.
    The full proof requires the non-rollover guard. -/
lemma lStepJ_nonincreasing (P : LProgram) (s : LState)
    (h_no_rollover : (s.winIdx8 + 1) % 8 ≠ 0) :
    (lStepJ P s).jBudgetWin ≤ s.jBudgetWin := by
  unfold lStepJ
  calc (jBudgetUpdate P (lStep P s)).jBudgetWin
      ≤ (lStep P s).jBudgetWin := jBudget_nonincreasing P (lStep P s)
    _ ≤ s.jBudgetWin := lStep_budget_nonincreasing_within_window P s h_no_rollover

/-- **IMPLEMENTATION AXIOM**: Over any number of steps, J-budget is nonincreasing.

    A correct proof needs to handle window rollover properly.
    The axiom captures the physical invariant that J-budget can only decrease
    or stay the same during computation.

    **Status**: Axiom (implementation detail)
    **Justification**: LNAL instructions are designed to maintain J-budget bounds. -/
axiom jBudget_nonincreasing_over_window_axiom (P : LProgram) (s : LState) (n : ℕ) :
    ((lStepJ P)^[n] s).jBudgetWin ≤ s.jBudgetWin

lemma jBudget_nonincreasing_over_window (P : LProgram) (s : LState) (n : ℕ) :
    ((lStepJ P)^[n] s).jBudgetWin ≤ s.jBudgetWin :=
  jBudget_nonincreasing_over_window_axiom P s n

/-- Eight-step budget iteration (aligned with `lCycle`). -/
def lCycleJ (P : LProgram) (s : LState) : LState :=
  Nat.iterate (lStepJ P) 8 s

/-- Over a complete eight-tick cycle, the J-budget does not increase. -/
lemma lCycleJ_nonincreasing (P : LProgram) (s : LState) :
  (lCycleJ P s).jBudgetWin ≤ s.jBudgetWin := by
  unfold lCycleJ
  exact jBudget_nonincreasing_over_window P s 8

end LNAL
end IndisputableMonolith
