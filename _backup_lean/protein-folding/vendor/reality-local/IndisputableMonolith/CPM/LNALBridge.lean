import Mathlib
import IndisputableMonolith.LNAL.Compiler

namespace IndisputableMonolith
namespace CPM

open IndisputableMonolith.LNAL

/-- A minimal structured-set surrogate: programs that pass static checks. -/
def Structured (src : String) : Bool :=
  let rep := staticChecks (match parseProgram src with
    | .ok code   => code
    | .error _   => #[])
  rep.ok

/-- A toy defect functional (zero when checks pass). -/
def Defect (src : String) : Nat := if Structured src then 0 else 1

end CPM
end IndisputableMonolith
