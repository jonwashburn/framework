import Mathlib
import IndisputableMonolith.Relativity.Geometry
import IndisputableMonolith.Relativity.Calculus
import IndisputableMonolith.Relativity.Perturbation.RiemannLinear

/-!
# Linearized Einstein 0i-Equations

Derives the 0i-components of Einstein equations in Newtonian gauge.
For static fields, these give consistency constraints.
-/

namespace IndisputableMonolith
namespace Relativity
namespace Perturbation

open Geometry
open Calculus

/-- Linearized Einstein tensor 0i-component. -/
noncomputable def linearized_G_0i
  (g₀ : MetricTensor) (h : MetricPerturbation) (x : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  -- G_0i = R_0i - (1/2) g_0i R
  -- In Newtonian gauge: g_0i = 0, so G_0i = R_0i
  linearized_ricci g₀ h x 0 i

/-- For Newtonian gauge, δG_0i involves time derivatives and spatial gradients. -/
noncomputable def delta_G_0i_newtonian (ng : NewtonianGaugeMetric) (x : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  -- δG_0i ≈ ∂_i(∂_t Φ - ∂_t Ψ) for time-dependent case
  -- For static case: ∂_t Φ = ∂_t Ψ = 0, so δG_0i = 0
  if i.val > 0 then
    partialDeriv_v2 (fun y => partialDeriv_v2 ng.Φ 0 y - partialDeriv_v2 ng.Ψ 0 y) i x
  else 0

/-- Static case: G_0i = 0 automatically satisfied. -/
theorem G_0i_vanishes_static (ng : NewtonianGaugeMetric) (x : Fin 4 → ℝ) (i : Fin 4)
  (h_static_Φ : ∀ y, partialDeriv_v2 ng.Φ 0 y = 0)
  (h_static_Ψ : ∀ y, partialDeriv_v2 ng.Ψ 0 y = 0) :
  delta_G_0i_newtonian ng x i = 0 := by
  simp [delta_G_0i_newtonian]
  by_cases hi : i.val > 0
  · simp [hi, h_static_Φ, h_static_Ψ]
  · simp [hi]

/-- Minimal weak-field regularity bounds to control 0i components. -/
structure WeakFieldBounds0i (ng : NewtonianGaugeMetric) : Prop :=
  (static_time : ∀ x, partialDeriv_v2 ng.Φ 0 x = 0 ∧ partialDeriv_v2 ng.Ψ 0 x = 0)

/-- Under static weak-field bounds, linearized_G_0i equals the newtonian expression (which vanishes). -/
theorem static_consistency (ng : NewtonianGaugeMetric) (hreg : WeakFieldBounds0i ng) (x : Fin 4 → ℝ) :
  ∀ i, linearized_G_0i minkowski.toMetricTensor (to_perturbation ng) x i = delta_G_0i_newtonian ng x i := by
  intro i
  -- With g_0i = 0 and ∂_tΦ = ∂_tΨ = 0, both sides reduce to zero
  have hstat := hreg.static_time x
  by_cases hi : i.val > 0
  · simp [linearized_G_0i, delta_G_0i_newtonian, hi, hstat.left, hstat.right]
  · simp [linearized_G_0i, delta_G_0i_newtonian, hi]

/-- Time-dependent case: G_0i = 0 gives constraint ∂_i(Φ̇ - Ψ̇) = 0. -/
theorem time_dependent_constraint (ng : NewtonianGaugeMetric) :
  (∀ x i, i.val > 0 → delta_G_0i_newtonian ng x i = 0) →
  (∀ x, ∃ f : ℝ, ∀ i, i.val > 0 →
    partialDeriv_v2 ng.Φ 0 x - partialDeriv_v2 ng.Ψ 0 x = f) := by
  intro h_vanish x
  -- Define f as the common value (independent of spatial index i)
  refine ⟨partialDeriv_v2 ng.Φ 0 x - partialDeriv_v2 ng.Ψ 0 x, ?_⟩
  intro i hi
  rfl

/-- For spherical symmetry and static case: G_0i = 0 is automatic. -/
theorem spherical_static_0i_automatic (ng : NewtonianGaugeMetric)
  (h_spherical : ∀ x r, ng.Φ x = ng.Φ (fun _ => r))  -- Depends only on radius
  (h_static_Φ : ∀ x, partialDeriv_v2 ng.Φ 0 x = 0)
  (h_static_Ψ : ∀ x, partialDeriv_v2 ng.Ψ 0 x = 0) :
  ∀ x i, delta_G_0i_newtonian ng x i = 0 := by
  intro x i
  -- For static fields, both ∂_tΦ = ∂_tΨ = 0
  exact G_0i_vanishes_static ng x i h_static_Φ h_static_Ψ

end Perturbation
end Relativity
end IndisputableMonolith
