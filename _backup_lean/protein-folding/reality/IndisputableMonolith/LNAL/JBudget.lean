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
def simulateBudget (code : Array LInstr) (init : Nat := 4) : Array Nat :=
  Id.run do
    let n := code.size
    let mut budget := init
    let mut out : Array Nat := Array.mkEmpty n
    for idx in [0:n] do
      -- `idx ∈ [0:n]` implies `idx < n`, but we keep this total by using `get?`.
      let instr := (code[idx]? ).getD (LInstr.simple Opcode.LOCK)
      let budget0 := if idx % 8 = 0 then init else budget
      let budget1 := stepBudget budget0 instr
      out := out.push budget1
      budget := budget1
    return out

/-- Budget is required to be nonincreasing within each 8-op window. -/
def jMonotoneWithinWindows (code : Array LInstr) (init : Nat := 4) : Bool :=
  let budgets := simulateBudget code init
  let n := budgets.size
  Id.run do
    let mut ok := true
    for i in [0:n] do
      if i + 1 < n ∧ (i / 8) = ((i + 1) / 8) then
        if budgets[i]! < budgets[i + 1]! then ok := false
    return ok

/-- Collect at most `k` violation indices where the budget increases within a window. -/
def jMonotoneViolations (code : Array LInstr) (init : Nat := 4) (k : Nat := 8) : List Nat :=
  let budgets := simulateBudget code init
  let n := budgets.size
  Id.run do
    let mut out : List Nat := []
    let mut ct : Nat := 0
    for i in [0:n] do
      if i + 1 < n ∧ (i / 8) = ((i + 1) / 8) then
        if budgets[i]! < budgets[i + 1]! ∧ ct < k then
          out := out.concat i
          ct := ct + 1
    return out

/-- Sum of positive costs per 8-op window (ΔJ bars used for reports). -/
def deltaJPerWindow (code : Array LInstr) : Array Nat :=
  Id.run do
    let n := code.size
    let windows := (n + 7) / 8
    let mut out : Array Nat := Array.mkEmpty windows
    for w in [0:windows] do
      let start := 8 * w
      let stop := min n (start + 8)
      let mut s : Nat := 0
      for i in [start:stop] do
        let instr := (code[i]? ).getD (LInstr.simple Opcode.LOCK)
        s := s + posCost instr
      out := out.push s
    return out

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
  simpa using (Nat.sub_le _ _)

end LNAL
end IndisputableMonolith
