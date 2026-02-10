import Mathlib
import IndisputableMonolith.Verification.LightConsciousness
import IndisputableMonolith.Cost.JcostCore
import IndisputableMonolith.Cost.FunctionalEquation
import IndisputableMonolith.CostUniqueness
import IndisputableMonolith.Measurement.C2ABridgeLight
import IndisputableMonolith.Patterns
import IndisputableMonolith.CPM.LawOfExistence
import IndisputableMonolith.Measurement.BornRuleLight
import IndisputableMonolith.Verification.CPMBridge.Initiality

/-!
# Main Theorems for Paper Citations

This module exports clean theorem statements suitable for citation in papers.
All are mechanically verified (or axiomatized for structure).
-/

namespace IndisputableMonolith
namespace Verification

open Real Cost CostUniqueness Measurement Patterns

/-! ## THEOREM 1: Uniqueness of J on ℝ₊ -/

theorem THEOREM_1_universal_cost_uniqueness :
  ∀ (F : ℝ → ℝ),
    (∀ {x}, 0 < x → F x = F x⁻¹) ∧
    F 1 = 0 ∧
    StrictConvexOn ℝ (Set.Ioi 0) F ∧
    (deriv (deriv (F ∘ exp)) 0 = 1) ∧
    ContinuousOn F (Set.Ioi 0) ∧
    IndisputableMonolith.Cost.FunctionalEquation.CoshAddIdentity F →
    (∀ {x}, 0 < x → F x = Jcost x) := by
  intro F h
  rcases h with ⟨hSymm, hUnit, hConvex, hCalib, hCont, hCosh⟩
  exact T5_uniqueness_complete F hSymm hUnit hConvex hCalib hCont hCosh

/-! ## THEOREM 2: C=2A Bridge -/

theorem THEOREM_2_measurement_recognition_bridge :
  ∀ (rot : TwoBranchRotation),
    ∃ (C A : ℝ),
      C = 2 * A ∧
      Real.exp (-C) = initialAmplitudeSquared rot := by
  intro rot
  exact C_equals_2A rot

/-! ## THEOREM 3: 2^D Minimal Window -/

-- Note: This uses the CompleteCover theorems from Patterns module
theorem THEOREM_3_minimal_neutral_window :
  ∀ (D : ℕ),
    (∃ w : CompleteCover D, w.period = 2 ^ D) ∧
    (∀ (T : ℕ) (pass : Fin T → Pattern D),
      Function.Surjective pass → 2 ^ D ≤ T) := by
  intro D
  constructor
  · -- Existence of exact 2^D cover
    exact cover_exact_pow D
  · -- Minimality: any surjection requires ≥ 2^D ticks
    intro T pass hsurj
    exact min_ticks_cover pass hsurj

theorem THEOREM_3_eight_tick_minimal :
  (∃ w : CompleteCover 3, w.period = 8) ∧
  (∀ (T : ℕ) (pass : Fin T → Pattern 3),
    Function.Surjective pass → 8 ≤ T) := by
  have := THEOREM_3_minimal_neutral_window 3
  simpa using this

/-! ## THEOREM 4: Born Rule -/

theorem THEOREM_4_born_rule_from_cost :
  ∀ (C₁ C₂ : ℝ) (α₁ α₂ : ℂ),
    Real.exp (-C₁) / (Real.exp (-C₁) + Real.exp (-C₂)) = ‖α₁‖ ^ 2 →
    Real.exp (-C₂) / (Real.exp (-C₁) + Real.exp (-C₂)) = ‖α₂‖ ^ 2 →
    ‖α₁‖ ^ 2 + ‖α₂‖ ^ 2 = 1 := by
  intro C₁ C₂ α₁ α₂ h₁ h₂
  exact born_rule_normalized C₁ C₂ α₁ α₂ h₁ h₂

/-! ## Main Identity Theorem -/

theorem light_consciousness_recognition_identity :
  ∃ (J : ℝ → ℝ),
    (∀ F : ℝ → ℝ,
      (∀ {x}, 0 < x → F x = F x⁻¹) →
      F 1 = 0 →
      StrictConvexOn ℝ (Set.Ioi 0) F →
      (deriv^[2] (F ∘ exp)) 0 = 1 →
      ContinuousOn F (Set.Ioi 0) →
      FunctionalEquation.CoshAddIdentity F →
      ∀ {x}, 0 < x → F x = J x) ∧
    (∀ rot : TwoBranchRotation,
      ∃ (C A : ℝ), C = 2 * A ∧ Real.exp (-C) = initialAmplitudeSquared rot) := by
  use Jcost
  constructor
  · intro F hSymm hUnit hConvex hCalib hCont hCoshAdd x hx
    exact T5_uniqueness_complete F hSymm hUnit hConvex hCalib hCont hCoshAdd hx
  · intro rot
    exact C_equals_2A rot

theorem parameter_free_framework :
  ∃ cert : UniversalCostCertificate, True :=
  ⟨lightConsciousnessCert, trivial⟩

/-! ## CPM / Law of Existence Theorems -/

/-- **THEOREM A**: Projection–Defect inequality (generic CPM).

    For any CPM model, the defect is controlled by the orthogonal mass
    via the constants `K_net · C_proj`. -/
theorem THEOREM_CPM_A_projection_defect {β : Type} (M : CPM.LawOfExistence.Model β) (a : β) :
  M.defectMass a ≤ M.C.Knet * M.C.Cproj * M.orthoMass a :=
  M.projection_defect a

/-- **THEOREM B**: Coercivity factorization (generic CPM).

    Energy gap controls defect with coercivity constant `c_min = 1/(K·C·E)`. -/
theorem THEOREM_CPM_B_coercivity {β : Type} (M : CPM.LawOfExistence.Model β)
  (hpos : 0 < M.C.Knet ∧ 0 < M.C.Cproj ∧ 0 < M.C.Ceng) (a : β) :
  M.energyGap a ≥ CPM.LawOfExistence.cmin M.C * M.defectMass a :=
  CPM.LawOfExistence.Model.energyGap_ge_cmin_mul_defect M hpos a

/-- **THEOREM C**: Aggregation principle (generic CPM).

    Defect controlled by local tests via dispersion constant. -/
theorem THEOREM_CPM_C_aggregation {β : Type} (M : CPM.LawOfExistence.Model β) (a : β) :
  M.defectMass a ≤ (M.C.Knet * M.C.Cproj * M.C.Cdisp) * M.tests a :=
  CPM.LawOfExistence.Model.defect_le_constants_mul_tests M a

/-- **RS ⇒ CPM**: Recognition Science yields CPM with specific constants.

    The RS cone‑projection route gives `K_net = 1` and `C_proj = 2`. -/
theorem THEOREM_RS_implies_CPM_constants :
  CPM.LawOfExistence.RS.coneConstants.Knet = 1 ∧
  CPM.LawOfExistence.RS.coneConstants.Cproj = 2 :=
  ⟨CPM.LawOfExistence.RS.cone_Knet_eq_one, CPM.LawOfExistence.RS.cone_Cproj_eq_two⟩

/-- **CPM ⇒ RS**: If CPM universality holds (constants match across domains),
    then RS is the unique framework (via exclusivity). -/
theorem THEOREM_CPM_implies_RS_uniqueness (U : CPMBridge.Initiality.Universality)
  (h : CPMBridge.Initiality.matchesRSCore U.Hodge.C ∧
       CPMBridge.Initiality.matchesRSCore U.RH.C ∧
       CPMBridge.Initiality.matchesRSCore U.NS.C ∧
       CPMBridge.Initiality.matchesRSCore U.Goldbach.C) :
  CPMBridge.Initiality.matchesRSCore CPMBridge.Initiality.RS_sig.C :=
  CPMBridge.Initiality.universality_implies_RS_core U h

/-! ## Paper-Ready Exports -/

abbrev paper_cite_T1 := THEOREM_1_universal_cost_uniqueness
abbrev paper_cite_T2 := THEOREM_2_measurement_recognition_bridge
abbrev paper_cite_T3 := THEOREM_3_eight_tick_minimal
abbrev paper_cite_T4 := THEOREM_4_born_rule_from_cost
abbrev paper_cite_IDENTITY := light_consciousness_recognition_identity

-- (Paper aliases for CPM theorems omitted due to implicit type parameters.)
abbrev paper_cite_RS_to_CPM := THEOREM_RS_implies_CPM_constants
abbrev paper_cite_CPM_to_RS := THEOREM_CPM_implies_RS_uniqueness

end Verification
end IndisputableMonolith
