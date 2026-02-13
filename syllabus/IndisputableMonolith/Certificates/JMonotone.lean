import Mathlib
import IndisputableMonolith.LNAL.Parser
import IndisputableMonolith.LNAL.JBudget

namespace IndisputableMonolith
namespace Certificates

open IndisputableMonolith.LNAL

/-- Certificate package for per-window J-budget monotonicity diagnostics. -/
structure JMonotoneCert where
  ok          : Bool
  initBudget  : Nat := 4
  budgets     : Array Nat := #[]
  deltaJ      : Array Nat := #[]
  violations  : List Nat := []
  errors      : List String := []
deriving Repr

@[simp] def JMonotoneCert.verified (c : JMonotoneCert) : Prop := c.ok = true

private def mkError (idxs : List Nat) : List String :=
  match idxs with
  | []      => []
  | (i::_)  =>
      let windowStart := (i / 8) * 8
      [s!"J-monotone violated within window starting at {windowStart} (first increase at step {i}→{i+1})"]

/-- Build a JMonotone certificate from compiled code. -/
def JMonotoneCert.fromProgram (code : Array LInstr) (initBudget : Nat := 4) : JMonotoneCert :=
  let budgets := simulateBudget code initBudget
  let delta := deltaJPerWindow code
  let violations := jMonotoneViolations code initBudget code.size
  let ok := violations = []
  let errors := if ok then [] else mkError violations
  { ok := ok, initBudget := initBudget, budgets := budgets, deltaJ := delta,
    violations := violations, errors := errors }

/-- Build a JMonotone certificate directly from LNAL source text. -/
def JMonotoneCert.fromSource (src : String) (initBudget : Nat := 4) : JMonotoneCert :=
  let code := match parseProgram src with
    | .ok code => code
    | .error _ => #[]
  fromProgram code initBudget

/-- Helper returning the first violation index, if any. -/
def JMonotoneCert.firstViolation? (c : JMonotoneCert) : Option Nat :=
  match c.violations with
  | [] => none
  | i :: _ => some i
