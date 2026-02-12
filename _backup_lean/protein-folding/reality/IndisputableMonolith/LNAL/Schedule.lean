import Mathlib
import Std.Data.List.Basic
import Std.Data.List.Lemmas
import IndisputableMonolith.LNAL.VM
import IndisputableMonolith.LNAL.JBudget
import IndisputableMonolith.LNAL.PhiIR

namespace IndisputableMonolith
namespace LNAL

/-- Alias for the canonical breath length (2^10). -/
@[simp] def breathLen : Nat := breathPeriod

/-- Midpoint tick index at which FLIP occurs in the reference schedule. -/
@[simp] def flipTick : Nat := breathLen / 2 - 1

lemma breathLen_pos : 0 < breathLen := by
  dsimp [breathLen, breathPeriod]
  decide

lemma flipTick_lt_breath : flipTick < breathLen := by
  dsimp [flipTick, breathLen, breathPeriod]
  decide

open Std

/-- Greedy ordering of windows by predicted ΔJ consumption. -/
structure JGreedyWindow where
  window : Nat
  gray   : Nat
  predictedDelta : Nat
  actualDelta : Nat
deriving Repr

/-- Score each 8-op window using ΔJ and sort descending (greedy heuristic). -/
def jGreedySchedule (code : Array LInstr) : List JGreedyWindow :=
  let deltas := JBudget.deltaJPerWindow code
  let windows := (deltas.toList.enum).map (fun (idx, delta) =>
    { window := idx,
      gray := PhiIR.grayIndex idx,
      predictedDelta := delta,
      actualDelta := delta : JGreedyWindow })
  windows.qsort (fun a b => a.predictedDelta > b.predictedDelta)

end LNAL
end IndisputableMonolith
