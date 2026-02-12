import Mathlib
import IndisputableMonolith.Verification.Exclusivity.Framework
import IndisputableMonolith.Verification.Exclusivity.IsomorphismDerivation
import IndisputableMonolith.Verification.Identifiability.Observations
import IndisputableMonolith.Verification.Necessity.PhiNecessity
import IndisputableMonolith.Verification.Exclusivity.NoAlternatives

namespace IndisputableMonolith
namespace Verification
namespace Exclusivity
namespace RSFramework

open Framework
open NoAlternatives
open Necessity

/-- Canonical zero-parameter framework packaged as a physics framework.
    We use the two-point Boolean space with dynamics `not`. -/
noncomputable def toPhysicsFramework (φ : ℝ) (F : RecogSpec.ZeroParamFramework φ) : PhysicsFramework where
  StateSpace := Bool
  evolve := not
  Observable := Unit
  measure := fun _ => ()
  hasInitialState := ⟨false⟩

instance (φ : ℝ) (F : RecogSpec.ZeroParamFramework φ) : Inhabited (toPhysicsFramework φ F).StateSpace := ⟨false⟩

instance (φ : ℝ) (F : RecogSpec.ZeroParamFramework φ) : NonStatic (toPhysicsFramework φ F) := by
  refine ⟨⟨false, ?_⟩⟩
  change Bool.not false ≠ false
  decide

/-- Canonical RS connection data for the Boolean flip physics framework built from
    a zero-parameter RS realization. This witnesses the structural isomorphism and
    observational agreement required by `RSConnectionData`. -/
noncomputable def canonicalConnection
    (φ : ℝ) (F : RecogSpec.ZeroParamFramework φ) :
    RSConnectionData (toPhysicsFramework φ F) :=
  {
    φ := φ
  , rsFramework := F
  , target := toPhysicsFramework φ F
  , iso :=
      {
        stateEquiv := Equiv.refl _
      , observableEquiv := Equiv.refl _
      , evolve_comm := by
          intro s; cases s <;> simp [toPhysicsFramework]
      , measure_comm := by
          intro s; cases s <;> simp [toPhysicsFramework]
      }
  , observedUD := Identifiability.observe_eq_ud φ F
  }

/-- Trivial derivation witnesses for the canonical physics framework. -/
noncomputable def derivesObservables (φ : ℝ) (F : RecogSpec.ZeroParamFramework φ) :
    DerivesObservables (toPhysicsFramework φ F) :=
  { derives_alpha := trivial
  , derives_masses := trivial
  , derives_constants := ⟨1, 1, 1, by constructor <;> norm_num⟩ }

/-- Trivial zero-parameter witness for the canonical physics framework. -/
noncomputable def hasZeroParameters (φ : ℝ) (F : RecogSpec.ZeroParamFramework φ) :
    HasZeroParameters (toPhysicsFramework φ F) := by
  classical
  refine ⟨
    { description := []
    , generates := fun n =>
        if n = 0 then some ([false] : List Bool)
        else if n = 1 then some [true]
        else none }
  , fun code =>
      if code = [false] then some false
      else if code = [true] then some true
      else none
  , ?_⟩
  intro s
  cases s
  · refine ⟨0, [false], by simp, by simp⟩
  · refine ⟨1, [true], by simp, by simp⟩

/-- Self-similarity witness for the canonical physics framework. -/
noncomputable def hasSelfSimilarity (φ : ℝ) (F : RecogSpec.ZeroParamFramework φ) :
    PhiNecessity.HasSelfSimilarity (toPhysicsFramework φ F).StateSpace :=
  { preferred_scale := Constants.phi
  , scale_gt_one := IndisputableMonolith.PhiSupport.one_lt_phi
  , level0 := 1
  , level1 := Constants.phi
  , level2 := Constants.phi ^ 2
  , level0_pos := by norm_num
  , level1_ratio := by simp
  , level2_ratio := by
      simp [pow_two, mul_comm, mul_left_comm, mul_assoc]
  , level2_recurrence := IndisputableMonolith.PhiSupport.phi_squared }

/-- Packaged assumptions used by the exclusivity pipeline.
    **DEPRECATED**: Uses circular RSConnectionData. Use rs_constraints_v2 instead. -/
noncomputable def rs_assumptions (φ : ℝ) (F : RecogSpec.ZeroParamFramework φ) :
    NoAlternativesAssumptions (toPhysicsFramework φ F) where
  nonStatic := inferInstance
  zeroParams := hasZeroParameters φ F
  derives := derivesObservables φ F
  selfSimilarity := hasSelfSimilarity φ F
  connection := canonicalConnection φ F

/-! ## Non-Circular Exclusivity Constraints (V2)

The following provides the RS framework representation compatible with
ExclusivityConstraintsV2 using the IsomorphismDerivation module.
-/

/-- The non-circular RS constraints are provided by IsomorphismDerivation.
    We re-export the key function for convenience. -/
noncomputable def rs_constraints_v2 (φ : ℝ) :
    ExclusivityConstraintsV2 (IsomorphismDerivation.rsPhysicsFramework φ) where
  inhabited := inferInstance
  zeroParams := IsomorphismDerivation.rs_has_zero_params φ
  selfSimilarity := {
    preferred_scale := Constants.phi
    scale_gt_one := IndisputableMonolith.PhiSupport.one_lt_phi
    level0 := 1
    level1 := Constants.phi
    level2 := Constants.phi ^ 2
    level0_pos := by norm_num
    level1_ratio := by simp
    level2_ratio := by simp [pow_two, mul_comm, mul_left_comm, mul_assoc]
    level2_recurrence := IndisputableMonolith.PhiSupport.phi_squared
  }
  obsCompat := {
    obsEquiv := Equiv.refl _
    exact_rs_match := fun _ => rfl
  }
  stateSubsingleton := inferInstance

end RSFramework
end Exclusivity
end Verification
end IndisputableMonolith
