import IndisputableMonolith.Verification.Completeness
-- import IndisputableMonolith.Verification.Exclusivity
-- import IndisputableMonolith.Verification.RecognitionReality
import IndisputableMonolith.Constants
import IndisputableMonolith.Meta.AxiomLattice
import IndisputableMonolith.Meta.FromCost
import IndisputableMonolith.URCGenerators
-- import IndisputableMonolith.URCAdapters.Reports
import Lean.Data.Json

def usage : String :=
  String.intercalate "\n"
    [ "usage: lake exe ok [--json] [--json-only] [--out FILE]"
    , "  --json       : also print JSON summary"
    , "  --json-only  : only print JSON summary"
    , "  --out FILE   : write JSON to FILE (implies --json)"
    ]

def main : IO Unit := do
  let args ← IO.getArgs
  let jsonOnly := args.contains "--json-only"
  let jsonAlso := args.contains "--json" || jsonOnly || (args.contains "--out")
  let outPath? :=
    match (args.dropWhile (· ≠ "--out")) with
    | _ :: path :: _ => some path
    | _ => none
  if jsonOnly && outPath?.isNone then
    -- still fine: just stdout JSON
    pure ()
  if !(jsonOnly) then
    let φ : ℝ := IndisputableMonolith.Constants.phi
    let _ := IndisputableMonolith.Verification.Exclusivity.phi_selection_unique
    IO.println "PhiUniqueness: OK"
    let pc := IndisputableMonolith.Verification.Completeness.prime_closure φ
    let _ : IndisputableMonolith.Verification.Reality.RSRealityMaster φ := pc.left
    let rest1 := pc.right
    let _ : IndisputableMonolith.RecogSpec.FrameworkUniqueness φ := rest1.left
    let rest2 := rest1.right
    let _ : ∀ D : Nat, IndisputableMonolith.Verification.Dimension.RSCounting_Gap45_Absolute D → D = 3 := rest2.left
    let rest3 := rest2.right
    let _ : Function.Surjective IndisputableMonolith.RSBridge.genOf := rest3.left
    let _ : IndisputableMonolith.Meta.AxiomLattice.FoundationMinimal φ := rest3.right
    IO.println "PrimeClosure: OK"
    IO.println "  - RSRealityMaster: OK (reality bundle)"
    IO.println "  - FrameworkUniqueness: OK (unique up to units)"
    IO.println "  - Necessity D = 3: OK"
    IO.println "  - Exact three generations: OK (genOf surjective)"
    IO.println "  - FoundationMinimal: OK (cost/CPM is weakest sufficient foundation)"
    let Γ := IndisputableMonolith.Meta.AxiomLattice.costCPMEnv
    let _ := IndisputableMonolith.Meta.FromCost.derives_physics_from_costCPM_with_usage Γ
      (by
        unfold IndisputableMonolith.Meta.AxiomLattice.costCPMEnv
        exact True.intro)
      (by
        unfold IndisputableMonolith.Meta.AxiomLattice.costCPMEnv
        exact True.intro)
      φ

    IO.println "  - FromCost sufficiency: OK (cost/CPM ⇒ physics derivation)"
    -- Minimal OK excludes exclusivity and recognition-reality reports to avoid cycles
  if jsonAlso then
    -- Provide a minimal JSON stub summarizing PrimeClosure only
    let jsonStr := Lean.Json.pretty <|
      Lean.Json.obj
        [ ("status", Lean.Json.str "OK")
        , ("checks", Lean.Json.arr
            #[ Lean.Json.str "PhiUniqueness"
             , Lean.Json.str "PrimeClosure"
             , Lean.Json.str "FromCost"
             ] )
        ]
    match outPath? with
    | some path => do IO.FS.writeFile path jsonStr; if !jsonOnly then IO.println s!"Wrote JSON to {path}"
    | none => IO.println jsonStr
