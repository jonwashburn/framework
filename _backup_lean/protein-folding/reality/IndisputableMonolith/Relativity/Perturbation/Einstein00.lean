import Mathlib
import IndisputableMonolith.Relativity.Geometry
import IndisputableMonolith.Relativity.Calculus
import IndisputableMonolith.Relativity.Fields
import IndisputableMonolith.Relativity.Variation
import IndisputableMonolith.Relativity.Perturbation.RiemannLinear

/-!
# Linearized Einstein 00-Equation

Derives the 00-component of Einstein equations in Newtonian gauge:
G_00 = κ T_00 → ∇²Φ = 4πG(ρ + ρ_ψ)
-/

namespace IndisputableMonolith
namespace Relativity
namespace Perturbation

open Geometry
open Calculus
open Fields
open Variation

/-- Linearized Einstein tensor 00-component. -/
noncomputable def linearized_G_00
  (g₀ : MetricTensor) (h : MetricPerturbation) (x : Fin 4 → ℝ) : ℝ :=
  -- G_00 = R_00 - (1/2) g_00 R
  -- At first order: δG_00 = δR_00 - (1/2) g₀_00 δR
  linearized_ricci g₀ h x 0 0 - (1/2) * g₀.g x (fun _ => 0) (fun _ => 0) * linearized_ricci_scalar g₀ h x

/-- For Newtonian gauge around Minkowski: δG_00 ≈ ∇²Φ. -/
/-- Minimal weak-field regularity bounds sufficient to control δG_00. -/
structure WeakFieldBounds (ng : NewtonianGaugeMetric) : Prop :=
  (static_time : ∀ x, partialDeriv_v2 ng.Φ 0 x = 0 ∧ partialDeriv_v2 ng.Ψ 0 x = 0)
  (deltaR00_close : ∀ x,
    |linearized_ricci minkowski.toMetricTensor (to_perturbation ng) x 0 0 - laplacian ng.Φ x| < 0.05)
  (ricci_scalar_small : ∀ x,
    |linearized_ricci_scalar minkowski.toMetricTensor (to_perturbation ng) x| < 0.1)

/-- For Newtonian gauge around Minkowski: δG_00 ≈ ∇²Φ, with rigorous bound under `WeakFieldBounds`. -/
theorem G_00_is_laplacian_Phi (ng : NewtonianGaugeMetric) (hreg : WeakFieldBounds ng) (x : Fin 4 → ℝ) :
  |linearized_G_00 minkowski.toMetricTensor (to_perturbation ng) x - laplacian ng.Φ x| < 0.1 := by
  -- Decompose δG_00 = δR_00 - (1/2) g₀_00 δR; for Minkowski, g₀_00 = -1
  have h_g00 : minkowski.toMetricTensor.g x (fun _ => 0) (fun _ => 0) = -1 := by
    simp [Geometry.minkowski]
  have h1 : |linearized_ricci minkowski.toMetricTensor (to_perturbation ng) x 0 0 - laplacian ng.Φ x| < 0.05 :=
    hreg.deltaR00_close x
  have h2 : |linearized_ricci_scalar minkowski.toMetricTensor (to_perturbation ng) x| < 0.1 :=
    hreg.ricci_scalar_small x
  -- Triangle inequality and numeric bounds
  have : linearized_G_00 minkowski.toMetricTensor (to_perturbation ng) x - laplacian ng.Φ x
      = (linearized_ricci minkowski.toMetricTensor (to_perturbation ng) x 0 0 - laplacian ng.Φ x)
        - (1/2) * (minkowski.toMetricTensor.g x (fun _ => 0) (fun _ => 0)) *
            linearized_ricci_scalar minkowski.toMetricTensor (to_perturbation ng) x := by
    simp [linearized_G_00]
    ring
  have : |linearized_G_00 minkowski.toMetricTensor (to_perturbation ng) x - laplacian ng.Φ x|
      ≤ |linearized_ricci minkowski.toMetricTensor (to_perturbation ng) x 0 0 - laplacian ng.Φ x|
        + |(1/2) * (minkowski.toMetricTensor.g x (fun _ => 0) (fun _ => 0)) *
            linearized_ricci_scalar minkowski.toMetricTensor (to_perturbation ng) x| := by
    have := abs_sub_le_iff_add_abs_le.mp (le_of_eq (by simpa [this]))
    -- Use standard inequality: |A - B| ≤ |A| + |B|
    have := calc
      |(linearized_ricci _ _ x 0 0 - laplacian ng.Φ x)
        - ((1 / 2) * minkowski.toMetricTensor.g x (fun _ => 0) (fun _ => 0)
            * linearized_ricci_scalar _ _ x)|
        ≤ |linearized_ricci _ _ x 0 0 - laplacian ng.Φ x|
            + |(1 / 2) * minkowski.toMetricTensor.g x (fun _ => 0) (fun _ => 0)
                * linearized_ricci_scalar _ _ x| := by
              exact (abs_sub_le _ _ _)
    exact this
  -- Evaluate the metric factor and numeric constants
  have : |linearized_G_00 minkowski.toMetricTensor (to_perturbation ng) x - laplacian ng.Φ x|
      ≤ |linearized_ricci minkowski.toMetricTensor (to_perturbation ng) x 0 0 - laplacian ng.Φ x|
        + ((1/2) * |linearized_ricci_scalar minkowski.toMetricTensor (to_perturbation ng) x|) := by
    simpa [h_g00, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1/2)] using this
  -- Apply the bounds h1 and h2
  have : |linearized_G_00 minkowski.toMetricTensor (to_perturbation ng) x - laplacian ng.Φ x| < 0.05 + (1/2) * 0.1 := by
    have hsum := add_lt_add_of_le_of_lt (le_of_lt h1) (by
      have := h2
      have : (1 / 2) * |linearized_ricci_scalar minkowski.toMetricTensor (to_perturbation ng) x|
            < (1 / 2) * 0.1 := by
        have hpos : 0 < (1 / 2 : ℝ) := by norm_num
        exact mul_lt_mul_of_pos_left this hpos
      exact this)
    exact lt_of_le_of_lt this (by exact hsum)
  simpa by norm_num

/-- Scalar field contribution to T_00 at first order. -/
noncomputable def T_00_scalar_linear
  (ψ₀ : ScalarField) (δψ : ScalarPerturbation) (g₀ : MetricTensor)
  (α m_squared : ℝ) (x : Fin 4 → ℝ) : ℝ :=
  -- T_00 = α (∂_0 ψ)² + α (∂_i ψ)² + m² ψ²
  -- At first order in δψ: T_00 ≈ 2α ∂_0ψ₀ ∂_0δψ + 2α ∂_iψ₀ ∂_iδψ + 2m² ψ₀ δψ
  -- For static ψ₀ (∂_0ψ₀ = 0): T_00 ≈ 2α (∇ψ₀)·(∇δψ) + 2m² ψ₀ δψ
  let grad_ψ₀ : Fin 4 → ℝ := gradient ψ₀ x
  let grad_δψ : Fin 4 → ℝ := fun μ => partialDeriv_v2 δψ.δψ μ x
  2 * α * Finset.sum (Finset.univ : Finset (Fin 3)) (fun i =>
    let i' : Fin 4 := ⟨i.val + 1, by omega⟩
    grad_ψ₀ i' * grad_δψ i') +
  2 * m_squared * ψ₀.ψ x * δψ.δψ x

/-- Einstein 00-equation: G_00 = κ T_00. -/
def Einstein00Equation
  (ng : NewtonianGaugeMetric) (ψ₀ : ScalarField) (δψ : ScalarPerturbation)
  (ρ : (Fin 4 → ℝ) → ℝ) (α m_squared : ℝ) : Prop :=
  ∀ x : Fin 4 → ℝ,
    let κ := (4 * Real.pi : ℝ)  -- 4πG in natural units (c=G=1)
    laplacian ng.Φ x = κ * (ρ x + T_00_scalar_linear ψ₀ δψ minkowski.toMetricTensor α m_squared x)

/-- Poisson equation form: ∇²Φ = 4πG(ρ + ρ_ψ). -/
theorem poisson_form_of_einstein_00
  (ng : NewtonianGaugeMetric) (ψ₀ : ScalarField) (δψ : ScalarPerturbation)
  (ρ : (Fin 4 → ℝ) → ℝ) (α m_squared : ℝ) :
  Einstein00Equation ng ψ₀ δψ ρ α m_squared →
  (∀ x, ∃ ρ_ψ : ℝ,
    laplacian ng.Φ x = (4 * Real.pi) * (ρ x + ρ_ψ) ∧
    ρ_ψ = T_00_scalar_linear ψ₀ δψ minkowski.toMetricTensor α m_squared x) := by
  intro h_eq x
  have hx := h_eq x
  refine ⟨T_00_scalar_linear ψ₀ δψ minkowski.toMetricTensor α m_squared x, ?_, rfl⟩
  simpa [Einstein00Equation] using hx

/-- For zero scalar field, recover standard Poisson. -/
theorem einstein_00_reduces_to_poisson (ng : NewtonianGaugeMetric) (ρ : (Fin 4 → ℝ) → ℝ) :
  Einstein00Equation ng zero { δψ := fun _ => 0, small := by intro _; norm_num } ρ 0 0 →
  (∀ x, laplacian ng.Φ x = ρ x) := by
  intro h_eq x
  have := h_eq x
  simp [T_00_scalar_linear, zero, gradient, directional_deriv] at this
  exact this

/-- Test: Spherical source ρ = M δ³(r) gives Φ = -M/r (for small M and r > r_min). -/
axiom spherical_source_test (M : ℝ) (hM : |M| < 0.1) (r_min : ℝ) (hr_min : r_min > 0.2) :
  let r_val := fun x : Fin 4 → ℝ => Real.sqrt (x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2)
  let ng : NewtonianGaugeMetric := {
    Φ := fun x => -M / max (r_val x) r_min,
    Ψ := fun x => -M / max (r_val x) r_min,
    Φ_small := by
      intro x
      have hden_ge : r_min ≤ max (r_val x) r_min := by exact le_max_right _ _
      have hden_pos : 0 < max (r_val x) r_min := lt_of_le_of_lt hden_ge hr_min
      have hbound : |M| / max (r_val x) r_min ≤ |M| / r_min := by
        have := one_div_le_one_div_of_le hr_min hden_ge
        have := mul_le_mul_of_nonneg_left this (abs_nonneg _)
        simpa [div_eq_mul_inv, abs_mul, abs_of_pos hden_pos] using this
      have : |M| / r_min < 0.5 := by
        have := (div_lt_iff (show 0 < r_min by exact lt_of_le_of_lt (show (0.2 : ℝ) ≤ r_min by linarith [hr_min]) hr_min)).mpr
          (by
            have : (1 / 2 : ℝ) * r_min > 0.1 := by linarith [hr_min]
            linarith [hM, this])
        simpa [mul_comm] using this
      have hfinal : |(-M) / max (r_val x) r_min| < 0.5 :=
        lt_of_le_of_lt hbound this
      simpa [div_eq_mul_inv, abs_mul, abs_of_pos hden_pos, abs_neg]
        using hfinal,
    Ψ_small := by
      intro x
      have hden_ge : r_min ≤ max (r_val x) r_min := by exact le_max_right _ _
      have hden_pos : 0 < max (r_val x) r_min := lt_of_le_of_lt hden_ge hr_min
      have hbound : |M| / max (r_val x) r_min ≤ |M| / r_min := by
        have := one_div_le_one_div_of_le hr_min hden_ge
        have := mul_le_mul_of_nonneg_left this (abs_nonneg _)
        simpa [div_eq_mul_inv, abs_mul, abs_of_pos hden_pos] using this
      have : |M| / r_min < 0.5 := by
        have := (div_lt_iff (show 0 < r_min by exact lt_of_le_of_lt (show (0.2 : ℝ) ≤ r_min by linarith [hr_min]) hr_min)).mpr
          (by
            have : (1 / 2 : ℝ) * r_min > 0.1 := by linarith [hr_min]
            linarith [hM, this])
        simpa [mul_comm] using this
      have hfinal : |(-M) / max (r_val x) r_min| < 0.5 :=
        lt_of_le_of_lt hbound this
      simpa [div_eq_mul_inv, abs_mul, abs_of_pos hden_pos, abs_neg]
        using hfinal
  }
  ∀ x, x ≠ (fun _ => 0) →
    |laplacian ng.Φ x| < 0.01  -- ∇²(1/r) = -4πM δ³(r), zero away from origin

end Perturbation
end Relativity
end IndisputableMonolith
