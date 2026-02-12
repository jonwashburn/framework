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

/-- **THEOREM**: LNAL budget monotonicity within a window.

    Each instruction in the LNAL VM is designed to either maintain or decrease
    the J-budget by consuming computational resources. Truncated subtraction
    in the state update ensures that the budget remains non-increasing.
    Window rollover, where the budget resets, is explicitly excluded by
    the non-rollover guard.

    **Proof structure**:
    1. If halted, state is unchanged, so budget unchanged.
    2. If not halted:
       - advIdx = (s.winIdx8 + 1) % 8
       - h_no_rollover ensures advIdx ≠ 0, so rollover = false
       - In all opcode cases, jBudgetWin := budget' where budget' = s.jBudgetWin - budgetDec
       - budgetNext := if rollover then jBudgetMax else s''.jBudgetWin
       - Since rollover = false, budgetNext = budget'
       - budget' = s.jBudgetWin - budgetDec ≤ s.jBudgetWin by Nat.sub_le -/
theorem lStep_budget_nonincreasing_within_window_thm (P : LProgram) (s : LState)
    (h_no_rollover : (s.winIdx8 + 1) % 8 ≠ 0) :
    (lStep P s).jBudgetWin ≤ s.jBudgetWin := by
  unfold lStep
  simp only [lFetch, lNextIP]
  by_cases hH : s.halted
  · -- Halted: state unchanged, so the budget is exactly the same
    simp only [hH, le_refl, ite_true]
  · -- Not halted: trace through the VM definition
    simp only [hH, ite_false]
    -- The lStep definition computes:
    -- 1. advIdx = (s.winIdx8 + 1) % 8 -- by h_no_rollover, advIdx ≠ 0
    -- 2. budget' = s.jBudgetWin - budgetDec (in all opcode branches)
    -- 3. s'.jBudgetWin = budget'
    -- 4. s'' preserves jBudgetWin from s'
    -- 5. rollover = (advIdx = 0) = false (by h_no_rollover)
    -- 6. budgetNext = if rollover then jBudgetMax else s''.jBudgetWin = s''.jBudgetWin
    -- 7. sFinal.jBudgetWin = budgetNext = budget' = s.jBudgetWin - budgetDec
    -- 8. The breath update preserves jBudgetWin
    -- 9. Final result ≤ s.jBudgetWin by Nat.sub_le
    --
    -- Abbreviations for the computation:
    set advIdx : Nat := (s.winIdx8 + 1) % 8
    -- Key: h_no_rollover says advIdx ≠ 0
    have h_advIdx_ne : advIdx ≠ 0 := h_no_rollover
    -- Therefore rollover = decide (advIdx = 0) = false
    have h_no_roll : decide (advIdx = 0) = false := by
      simp only [decide_eq_false_iff_not, h_advIdx_ne, not_false_eq_true]

    -- Key: when advIdx ≠ 0, the if-then-else selects s''.jBudgetWin, not jBudgetMax
    -- Since h_no_roll: (advIdx = 0) = false, the budgetNext branch selects s''.jBudgetWin

    -- Expand the goal using the structure of lStep
    -- The final jBudgetWin = budgetNext where:
    -- budgetNext = if advIdx = 0 then s''.jBudgetMax else s''.jBudgetWin
    --            = s''.jBudgetWin (since advIdx ≠ 0)
    --            = budget' = s.jBudgetWin - budgetDec

    -- Use simp to partially reduce, then split on opcode
    simp only [h_no_roll, ↓reduceIte, Bool.false_eq_true]

    -- Now the goal shows the full expanded structure.
    -- Each opcode case has jBudgetWin := s.jBudgetWin - (instrCost (P s.ip)).toNat
    -- Split on the opcode and apply Nat.sub_le in each case
    cases (P s.ip).op <;> simp only [Nat.sub_le]

/-- **LEMMA**: lStep preserves jBudgetMax in all cases.
    The jBudgetMax field is never modified by lStep. -/
lemma lStep_preserves_jBudgetMax (P : LProgram) (s : LState) :
    (lStep P s).jBudgetMax = s.jBudgetMax := by
  unfold lStep
  simp only [lFetch, lNextIP]
  by_cases hH : s.halted
  · simp only [hH, ite_true]
  · simp only [hH, ite_false]
    -- Trace through the structure: all opcode branches preserve jBudgetMax
    cases (P s.ip).op <;> rfl

/-- **LEMMA**: jBudgetUpdate preserves jBudgetMax. -/
lemma jBudgetUpdate_preserves_jBudgetMax (P : LProgram) (s : LState) :
    (jBudgetUpdate P s).jBudgetMax = s.jBudgetMax := by
  unfold jBudgetUpdate jBudgetUpdateStep
  rfl

/-- **LEMMA**: lStepJ preserves jBudgetMax. -/
lemma lStepJ_preserves_jBudgetMax (P : LProgram) (s : LState) :
    (lStepJ P s).jBudgetMax = s.jBudgetMax := by
  unfold lStepJ
  rw [jBudgetUpdate_preserves_jBudgetMax, lStep_preserves_jBudgetMax]

/-- **LEMMA**: Iterating lStepJ preserves jBudgetMax. -/
lemma iterate_lStepJ_preserves_jBudgetMax (P : LProgram) (s : LState) (n : ℕ) :
    ((lStepJ P)^[n] s).jBudgetMax = s.jBudgetMax := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ']
    simp only [Function.comp_apply]
    rw [lStepJ_preserves_jBudgetMax, ih]

/-- **LEMMA**: On rollover, lStep sets jBudgetWin to jBudgetMax (when not halted). -/
lemma lStep_rollover_sets_jBudgetMax (P : LProgram) (s : LState)
    (h_not_halted : ¬s.halted) (h_rollover : (s.winIdx8 + 1) % 8 = 0) :
    (lStep P s).jBudgetWin = s.jBudgetMax := by
  unfold lStep
  simp only [lFetch, lNextIP, h_not_halted, ite_false]
  -- Now we have the expanded non-halted branch
  -- advIdx = (s.winIdx8 + 1) % 8 = 0 (by h_rollover)
  set advIdx := (s.winIdx8 + 1) % 8 with hadv
  have h_advIdx_zero : advIdx = 0 := h_rollover
  -- rollover = (advIdx = 0) = true
  have h_roll_true : decide (advIdx = 0) = true := by
    simp only [decide_eq_true_iff, h_advIdx_zero]
  simp only [h_roll_true, ite_true]
  -- Now the budgetNext branch selects jBudgetMax
  cases (P s.ip).op <;> rfl

/-- **THEOREM**: LNAL total budget monotonicity when starting at window boundary.

    When starting with budget = jBudgetMax (window boundary), the J-budget
    is non-increasing over any number of steps.

    **Proof structure**:
    - Base case: n=0, budget unchanged
    - Inductive case: jBudgetUpdate can only decrease or maintain budget (Nat.sub_le)
    - On rollover, budget resets to jBudgetMax ≤ s.jBudgetWin (by h_start)
    - So the invariant jBudgetWin ≤ initial is preserved -/
theorem jBudget_nonincreasing_over_window_from_max (P : LProgram) (s : LState) (n : ℕ)
    (h_start : s.jBudgetWin = s.jBudgetMax) :
    ((lStepJ P)^[n] s).jBudgetWin ≤ s.jBudgetWin := by
  induction n with
  | zero => simp
  | succ k ih =>
    -- ((lStepJ P)^[k+1] s).jBudgetWin = (lStepJ P ((lStepJ P)^[k] s)).jBudgetWin
    rw [Function.iterate_succ']
    -- Need: (lStepJ P ((lStepJ P)^[k] s)).jBudgetWin ≤ s.jBudgetWin
    -- By IH: ((lStepJ P)^[k] s).jBudgetWin ≤ s.jBudgetWin
    -- And lStepJ is non-increasing (jBudget_nonincreasing + lStep effects)
    -- Key: on rollover, budget resets to jBudgetMax = s.jBudgetMax ≤ s.jBudgetWin = s.jBudgetMax ✓
    -- Requires: showing jBudgetMax is preserved or bounded properly
    --
    -- The proof uses transitivity:
    -- (lStepJ P (iter^k s)).jBudgetWin ≤ (iter^k s).jBudgetWin  (by jBudget_nonincreasing)
    --                                  ≤ s.jBudgetWin            (by IH)
    --
    -- Note: jBudget_nonincreasing applies to jBudgetUpdate, but lStepJ = jBudgetUpdate ∘ lStep.
    -- The lStep can increase budget on rollover, but jBudgetUpdate then decreases it.
    -- For the full proof, we need to track both effects.
    --
    -- Simplified approach: use the axiom for now (this is the theorem we're trying to prove)
    -- The full proof requires showing lStepJ preserves the ≤ relation.
    have h_step := jBudget_nonincreasing P ((lStepJ P)^[k] s)
    calc (lStepJ P ((lStepJ P)^[k] s)).jBudgetWin
      _ = (jBudgetUpdate P (lStep P ((lStepJ P)^[k] s))).jBudgetWin := rfl
      _ ≤ (lStep P ((lStepJ P)^[k] s)).jBudgetWin := jBudget_nonincreasing P (lStep P ((lStepJ P)^[k] s))
      _ ≤ s.jBudgetWin := by
        -- Need: (lStep P (iter^k s)).jBudgetWin ≤ s.jBudgetWin
        --
        -- The proof uses the structure of lStep:
        -- Case 1: No rollover → budget decreases → (lStep s').jBudgetWin ≤ s'.jBudgetWin ≤ s.jBudgetWin
        -- Case 2: Rollover → budget = jBudgetMax → need jBudgetMax ≤ s.jBudgetWin
        --
        -- Key insight: lStep preserves jBudgetMax (it's not modified in lStep)
        -- And h_start: s.jBudgetWin = s.jBudgetMax
        -- So on rollover: (lStep s').jBudgetWin = s'.jBudgetMax = s.jBudgetMax = s.jBudgetWin
        --
        -- For non-rollover, we use transitivity with IH.
        --
        -- The formal proof requires:
        -- 1. Helper lemma: lStep_preserves_jBudgetMax
        -- 2. Case split on rollover condition
        -- 3. Chain the inequalities
        --
        -- Proof outline:
        -- let s' := (lStepJ P)^[k] s
        -- Case on rollover at (lStep P s'):
        -- - If no rollover: (lStep P s').jBudgetWin = s'.jBudgetWin - budgetDec ≤ s'.jBudgetWin ≤ s.jBudgetWin (by ih)
        -- - If rollover: (lStep P s').jBudgetWin = s'.jBudgetMax
        --               Since lStep preserves jBudgetMax: s'.jBudgetMax = s.jBudgetMax
        --               By h_start: s.jBudgetMax = s.jBudgetWin
        --               So (lStep P s').jBudgetWin = s.jBudgetWin ✓
        set s' := (lStepJ P)^[k] s with hs'
        -- Case split on rollover condition
        by_cases h_roll : (s'.winIdx8 + 1) % 8 = 0
        · -- Rollover case: budget resets to jBudgetMax
          -- Need to show (lStep P s').jBudgetWin ≤ s.jBudgetWin
          -- Since jBudgetMax is preserved: s'.jBudgetMax = s.jBudgetMax
          -- And h_start: s.jBudgetWin = s.jBudgetMax
          have h_max_preserved : s'.jBudgetMax = s.jBudgetMax := iterate_lStepJ_preserves_jBudgetMax P s k
          -- Handle halted case first
          by_cases h_halted : s'.halted
          · -- If halted, lStep P s' = s' (with breath update), budget unchanged
            -- (lStep P s').jBudgetWin = s'.jBudgetWin ≤ s.jBudgetWin (by ih)
            unfold lStep at *
            simp only [lFetch, lNextIP, h_halted, ite_true] at *
            exact ih
          · -- Not halted: use lStep_rollover_sets_jBudgetMax
            have h_eq : (lStep P s').jBudgetWin = s.jBudgetWin := by
              calc (lStep P s').jBudgetWin
                _ = s'.jBudgetMax := lStep_rollover_sets_jBudgetMax P s' h_halted h_roll
                _ = s.jBudgetMax := h_max_preserved
                _ = s.jBudgetWin := h_start.symm
            exact le_of_eq h_eq
        · -- Non-rollover case: budget decreases by Nat.sub_le
          have h_no_roll : (s'.winIdx8 + 1) % 8 ≠ 0 := h_roll
          calc (lStep P s').jBudgetWin
            _ ≤ s'.jBudgetWin := lStep_budget_nonincreasing_within_window_thm P s' h_no_roll
            _ ≤ s.jBudgetWin := ih

/-- Eight-step budget iteration (aligned with `lCycle`). -/
def lCycleJ (P : LProgram) (s : LState) : LState :=
  Nat.iterate (lStepJ P) 8 s

/-- Over a complete eight-tick cycle starting from window max, the J-budget does not increase. -/
lemma lCycleJ_nonincreasing (P : LProgram) (s : LState)
    (h_start : s.jBudgetWin = s.jBudgetMax) :
    (lCycleJ P s).jBudgetWin ≤ s.jBudgetWin := by
  unfold lCycleJ
  exact jBudget_nonincreasing_over_window_from_max P s 8 h_start

end LNAL
end IndisputableMonolith
