import Mathlib
import IndisputableMonolith.LNAL.Parser
import IndisputableMonolith.LNAL.Compiler

open IndisputableMonolith
open IndisputableMonolith.LNAL

namespace CI_CLI

/-- Minimal CLI-smoke equivalent: build a tiny valid program and run staticChecks. -/
def main : IO UInt32 := do
  let src := String.intercalate "\n"
    [ "SEED"
    , "GC_SEED"
    , "FOLD"
    , "UNFOLD"
    , "BALANCE"
    , "FLIP"
    , "VECTOR_EQ"
    ]
  match parseProgramFull src with
  | .error e => IO.eprintln s!"[LNALCliSmoke][FAIL] Parse error: {repr e}"; return 1
  | .ok out =>
      let rep := staticChecks out.code out.phi out.packets
      if rep.ok then
        IO.println "[LNALCliSmoke] ✓ check-only OK"
        return 0
      else
        IO.eprintln s!"[LNALCliSmoke][FAIL] {String.intercalate "; " rep.errors}"
        return 2

end CI_CLI
