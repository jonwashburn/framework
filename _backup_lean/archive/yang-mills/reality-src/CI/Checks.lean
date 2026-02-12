import IndisputableMonolith.Constants
import IndisputableMonolith.Verification.Completeness
import IndisputableMonolith.Verification.Exclusivity
import IndisputableMonolith.Verification.RecognitionReality
import IndisputableMonolith.URCGenerators
import IndisputableMonolith.RH.RS.Spec

/-!
  CI checks: force-elaborate critical theorems and print OK markers.

  This executable should remain lightweight but is allowed to import the
  verification surface needed to elaborate the target theorems.
-/

def main : IO Unit := do
  let φ : ℝ := IndisputableMonolith.Constants.phi

  -- 1) PrimeClosure at φ (apex certificate) – elaboration forces all conjuncts
  let _pc : IndisputableMonolith.Verification.Completeness.PrimeClosure φ :=
    IndisputableMonolith.Verification.Completeness.prime_closure φ
  IO.println "PrimeClosure: OK"

  -- 2) ExclusiveRealityPlus (unique φ; exclusivity + bi-interpretability)
  let _ := IndisputableMonolith.Verification.Exclusivity.exclusive_reality_plus_holds
  IO.println "ExclusiveRealityPlus: OK"

  -- 3) RecognitionReality accessors (phi/master/defUnique/bi)
  let _φ⋆ := IndisputableMonolith.Verification.RecognitionReality.recognitionReality_phi
  let _ := IndisputableMonolith.Verification.RecognitionReality.recognitionReality_at
  let _ := IndisputableMonolith.Verification.RecognitionReality.recognitionReality_master
  let _ := IndisputableMonolith.Verification.RecognitionReality.recognitionReality_definitionalUniqueness
  let _ := IndisputableMonolith.Verification.RecognitionReality.recognitionReality_bi
  IO.println "RecognitionRealityAccessors: OK"

  -- 4) φ uniqueness under selection (+ recognition closure uniqueness bundle)
  let _ := IndisputableMonolith.RH.RS.phi_selection_unique_holds
  let _ := IndisputableMonolith.URCGenerators.phi_selection_unique_with_closure
  IO.println "PhiUniqueness: OK"

  -- 5) UltimateClosure at the pinned φ
  let _ := IndisputableMonolith.Verification.RecognitionReality.ultimate_closure_holds
  IO.println "UltimateClosure: OK"
