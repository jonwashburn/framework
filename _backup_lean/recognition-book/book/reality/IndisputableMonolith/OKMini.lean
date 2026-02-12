import IndisputableMonolith.Verification.Completeness
import IndisputableMonolith.Constants
import Lean.Data.Json

open IndisputableMonolith

def main : IO Unit := do
  let φ : ℝ := Constants.phi
  let _ := Verification.Completeness.prime_closure φ
  IO.println "PrimeClosure: OK"
  -- Minimal JSON summary
  let jsonStr := Lean.Json.pretty <|
    Lean.Json.obj [ ("PrimeClosure", Lean.Json.str "OK") ]
  IO.println jsonStr
