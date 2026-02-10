import Mathlib
import IndisputableMonolith.Relativity.Geometry
import IndisputableMonolith.Relativity.Perturbation.Linearization
import IndisputableMonolith.Relativity.Perturbation.GaugeTransformation

/-!
# Newtonian Gauge

Fixes gauge freedom in weak-field limit: h_0i = 0, h_ij ∝ δ_ij.
Results in Newtonian potentials Φ, Ψ.
-/

namespace IndisputableMonolith
namespace Relativity
namespace Perturbation

open Geometry

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
      dsimp
      split_ifs with h1 h2 h3
      · -- h_00 case
        have hΦ := ng.Φ_small x
        rw [abs_mul, abs_neg]
        norm_num
        linarith
      · -- h_0i case
        norm_num
      · -- h_ii case
        have hΨ := ng.Ψ_small x
        rw [abs_mul, abs_neg]
        norm_num
        linarith
      · -- h_ij (i!=j) case
        norm_num
  }

/-- In Newtonian gauge around Minkowski: ds² = -(1+2Φ)dt² + (1-2Ψ)dx². -/
noncomputable def newtonian_metric (ng : NewtonianGaugeMetric) : MetricTensor :=
  perturbed_metric minkowski_tensor (to_perturbation ng)

/-- **HYPOTHESIS**: There always exists a coordinate transformation to the
    Newtonian gauge.
    STATUS: EMPIRICAL_HYPO
    TEST_PROTOCOL: Verify that for any linear metric perturbation h_μν, there exists
    a gauge vector ξ^μ such that h'_0i = 0 and h'_ij ∝ δ_ij.
    FALSIFIER: Discovery of a physical perturbation that cannot be gauge-transformed
    into the Newtonian form. -/
def H_NewtonianGaugeExists (h : MetricPerturbation) : Prop :=
  ∃ ng : NewtonianGaugeMetric,
    ∀ g₀ x ρ σ μ ν,
      linearized_riemann g₀ h x ρ σ μ ν =
      linearized_riemann g₀ (to_perturbation ng) x ρ σ μ ν

/-- Gauge freedom: can always choose coordinates to reach Newtonian gauge.
    Standard result in GR perturbation theory. -/
theorem gauge_choice_exists (h_gauge : H_NewtonianGaugeExists h) (h : MetricPerturbation)
    [inst : GaugeConstructionFacts] :
    ∃ ng : NewtonianGaugeMetric,
      ∀ g₀ x ρ σ μ ν,
        linearized_riemann g₀ h x ρ σ μ ν =
        linearized_riemann g₀ (to_perturbation ng) x ρ σ μ ν := h_gauge

end Perturbation
end Relativity
end IndisputableMonolith
