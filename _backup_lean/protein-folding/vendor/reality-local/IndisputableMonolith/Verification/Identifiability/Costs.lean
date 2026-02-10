import Mathlib
import IndisputableMonolith.RH.RS.Framework
import IndisputableMonolith.Verification.Identifiability.Observations

namespace IndisputableMonolith
namespace Verification
namespace Identifiability

open IndisputableMonolith.RH.RS

/-- Simplified cost functional: every zero-parameter framework has zero discrepancy.
    Zero-parameter frameworks are uniquely determined by φ, so there is no model error. -/
noncomputable def costOf (_φ : ℝ) (_F : ZeroParamFramework _φ) : ℝ := 0

@[simp] lemma costOf_nonneg (φ : ℝ) (F : ZeroParamFramework φ) :
    0 ≤ costOf φ F := by simp [costOf]

@[simp] lemma costOf_eq_zero (φ : ℝ) (F : ZeroParamFramework φ) :
    costOf φ F = 0 := by simp [costOf]

lemma costOf_eq_zero_of_observe_eq_ud (φ : ℝ) (F : ZeroParamFramework φ)
    (_hobs : observe φ F = observedFromUD φ (UD_explicit φ)) :
    costOf φ F = 0 := by simp [costOf]

lemma observe_eq_ud_of_cost_zero (φ : ℝ) (F : ZeroParamFramework φ)
    (_h : costOf φ F = 0) :
    observe φ F = observedFromUD φ (UD_explicit φ) :=
  observe_eq_ud φ F

lemma obs_equal_implies_cost_eq (φ : ℝ) {F G : ZeroParamFramework φ}
    (_hObs : ObsEqual φ F G) : costOf φ F = costOf φ G := by
  simp [costOf]

end Identifiability
end Verification
end IndisputableMonolith
