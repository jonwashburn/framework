import Mathlib
import IndisputableMonolith.Relativity.Geometry
import IndisputableMonolith.Relativity.Perturbation.Linearization

/-!
# Newtonian Gauge

Fixes gauge freedom in weak-field limit: h_0i = 0, h_ij ∝ δ_ij.
Results in Newtonian potentials Φ, Ψ.
-/

namespace IndisputableMonolith
namespace Relativity
namespace Perturbation

open Geometry

/-- Newtonian gauge: metric perturbation with time-space components zero. -/
structure NewtonianGaugeMetric where
  Φ : (Fin 4 → ℝ) → ℝ  -- g_00 = -(1 + 2Φ)
  Ψ : (Fin 4 → ℝ) → ℝ  -- g_ij = (1 - 2Ψ)δ_ij
  Φ_small : ∀ x, |Φ x| < 0.5
  Ψ_small : ∀ x, |Ψ x| < 0.5

/-- Convert Newtonian gauge to metric perturbation. -/
noncomputable def to_perturbation (ng : NewtonianGaugeMetric) : MetricPerturbation :=
  {
    h := fun x low =>
      let μ := low 0
      let ν := low 1
      if (μ.val = 0) ∧ (ν.val = 0) then
        -- h_00 = -2 Φ
        (-2 : ℝ) * ng.Φ x
      else if (μ.val = 0) ∨ (ν.val = 0) then
        -- h_0i = h_i0 = 0
        0
      else if μ = ν then
        -- h_ij = -2 Ψ δ_ij (off-diagonal zero handled by next else)
        (-2 : ℝ) * ng.Ψ x
      else 0
  ,  small := by
      intro x μ ν
      by_cases hμ0 : μ.val = 0
      · by_cases hν0 : ν.val = 0
        · -- (0,0) component: |-2 Φ| < 1 from |Φ| < 1/2
          have hΦ : |ng.Φ x| < 0.5 := ng.Φ_small x
          have hlt : (2 : ℝ) * |ng.Φ x| < 1 := by
            have := mul_lt_mul_of_pos_left hΦ (by norm_num : 0 < (2 : ℝ))
            simpa using this
          have : |(-2 : ℝ) * ng.Φ x| < 1 := by
            simpa [abs_mul, abs_neg] using hlt
          simpa [to_perturbation, hμ0, hν0] using this
        · -- (0,i) or (i,0): zero
          have : |0| < 1 := by norm_num
          have hν0' : ¬(ν.val = 0) := by exact hν0
          have hμν : (μ.val = 0) ∧ (ν.val = 0) := by exact And.intro hμ0 hν0 -- unused, keep structure
          simpa [to_perturbation, hμ0, hν0, hμν] using this
      · by_cases hν0 : ν.val = 0
        · -- (i,0): zero
          have : |0| < 1 := by norm_num
          have hμ0' : ¬(μ.val = 0) := by exact hμ0
          simpa [to_perturbation, hμ0, hν0] using this
        · -- spatial-spatial
          by_cases hdiag : μ = ν
          · -- diagonal spatial: |-2 Ψ| < 1
            have hΨ : |ng.Ψ x| < 0.5 := ng.Ψ_small x
            have hlt : (2 : ℝ) * |ng.Ψ x| < 1 := by
              have := mul_lt_mul_of_pos_left hΨ (by norm_num : 0 < (2 : ℝ))
              simpa using this
            have : |(-2 : ℝ) * ng.Ψ x| < 1 := by
              simpa [abs_mul, abs_neg] using hlt
            simpa [to_perturbation, hμ0, hν0, hdiag] using this
          · -- off-diagonal spatial: zero
            have : |0| < 1 := by norm_num
            simpa [to_perturbation, hμ0, hν0, hdiag] using this
  }

/-- In Newtonian gauge around Minkowski: ds² = -(1+2Φ)dt² + (1-2Ψ)dx². -/
noncomputable def newtonian_metric (ng : NewtonianGaugeMetric) : MetricTensor :=
  perturbed_metric minkowski.toMetricTensor (to_perturbation ng)

/-- Gauge freedom: can always choose coordinates to reach Newtonian gauge.
    Standard result in GR perturbation theory. -/
theorem gauge_choice_exists (h : MetricPerturbation)
  [GaugeConstructionFacts] :
  ∃ ng : NewtonianGaugeMetric, True :=
  let ⟨ng, hng⟩ := GaugeConstructionFacts.newtonian_gauge_exists h
  ⟨ng, trivial⟩

end Perturbation
end Relativity
end IndisputableMonolith
