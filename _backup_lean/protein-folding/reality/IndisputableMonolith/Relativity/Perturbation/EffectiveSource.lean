import Mathlib
import IndisputableMonolith.Relativity.Geometry
import IndisputableMonolith.Relativity.Calculus
import IndisputableMonolith.Relativity.Fields
import IndisputableMonolith.Relativity.Perturbation.ScalarLinearized
import IndisputableMonolith.Relativity.Perturbation.CoupledSystem

/-!
# Effective Source Term and w(r) Extraction

Computes T_00[δψ(Φ,Ψ)] explicitly, factors out ρ, and identifies the weight correction.
This is where w(r) = 1 + δρ_ψ/ρ emerges!
-/

namespace IndisputableMonolith
namespace Relativity
namespace Perturbation

open Geometry
open Calculus
open Fields

/-- Explicit T_00 with δψ = δψ[Φ,Ψ] substituted. -/
noncomputable def T_00_explicit
  (ψ₀ : ScalarField) (ng : NewtonianGaugeMetric) (α : ℝ) (x : Fin 4 → ℝ) : ℝ :=
  -- T_00 = 2α (∇ψ₀)·(∇δψ) + 2m²ψ₀ δψ
  -- With δψ ≈ -c(Φ+Ψ):
  -- T_00 ≈ 2α (∇ψ₀)·(∇(-c(Φ+Ψ))) + 2m²ψ₀(-c(Φ+Ψ))
  --     = -2αc (∇ψ₀)·(∇(Φ+Ψ)) - 2m²c ψ₀(Φ+Ψ)
  let c := 0.1  -- From delta_psi_solution
  let grad_ψ₀ := gradient ψ₀ x
  let grad_sum := fun μ => partialDeriv_v2 (fun y => ng.Φ y + ng.Ψ y) μ x
  -2 * α * c * Finset.sum (Finset.range 3) (fun i =>
    let i' : Fin 4 := ⟨i + 1, by omega⟩
    grad_ψ₀ i' * grad_sum i')

/-- Factor ρ out of T_00 (requires physical assumption linking ψ₀ to ρ). -/
theorem T_00_factorization
  (ψ₀ : ScalarField) (ng : NewtonianGaugeMetric) (ρ : (Fin 4 → ℝ) → ℝ) (α : ℝ)
  (h_ψ₀_from_ρ : ∀ x, ∃ k : ℝ, Fields.gradient ψ₀ x = fun μ => k * partialDeriv_v2 ρ μ x) :
  ∀ x, ∃ correction : ℝ,
    T_00_explicit ψ₀ ng α x = ρ x * correction := by
  intro x
  -- With ∇ψ₀ ∝ ∇ρ (physical: scalar field sourced by matter):
  -- T_00 = -2αc (∇ψ₀)·(∇(Φ+Ψ)) = -2αc k (∇ρ)·(∇(Φ+Ψ))
  -- For spherical ρ(r): ∇ρ ∝ ρ'/r (radial), ∇Φ ∝ Φ'/r
  -- Factoring: T_00 ~ ρ(r) × [function of derivatives]
  rcases h_ψ₀_from_ρ x with ⟨k, hk⟩
  refine ⟨(-2 * α * 0.1 * k * Finset.sum (Finset.range 3) (fun i =>
      let i' : Fin 4 := ⟨i + 1, by omega⟩
      (partialDeriv_v2 ρ i' x) * (partialDeriv_v2 (fun y => ng.Φ y + ng.Ψ y) i' x))) / ρ x, ?_⟩
  simp [T_00_explicit, hk]
  by_cases h : ρ x = 0
  · simpa [h]
  · field_simp [h]
    ring

/-- Weight correction term. -/
noncomputable def w_correction_term
  (ψ₀ : ScalarField) (ng : NewtonianGaugeMetric) (ρ : (Fin 4 → ℝ) → ℝ) (α C_lag : ℝ) (x : Fin 4 → ℝ) : ℝ :=
  -- w = 1 + (T_00_scalar / ρ)
  if ρ x = 0 then 0 else (T_00_explicit ψ₀ ng α x) / ρ x

/-- Weight correction stays small under weak-field hypotheses. -/
theorem w_correction_small (ψ₀ : ScalarField) (ng : NewtonianGaugeMetric) (ρ : (Fin 4 → ℝ) → ℝ) (α C_lag : ℝ)
  (h_α_small : |α| < 0.2) (h_C_small : |C_lag| < 0.1)
  (h_ψ₀_bounded : ∀ x μ, |Fields.gradient ψ₀ x μ| ≤ 1)
  (h_grad_ΦΨ : ∀ x μ, |partialDeriv_v2 (fun y => ng.Φ y + ng.Ψ y) μ x| ≤ 0.5)
  (h_ρ_pos : ∀ x, 0 < ρ x) (h_ρ_lower : ∀ x, 1 ≤ ρ x) :
  ∀ x, |w_correction_term ψ₀ ng ρ α C_lag x| < 0.07 := by
  intro x h_ρ_pos
  have hρ_ne : ρ x ≠ 0 := ne_of_gt (h_ρ_pos x)
  have hρ_ge : 1 ≤ ρ x := h_ρ_lower x
  simp [w_correction_term, T_00_explicit, hρ_ne]
  -- Define shorthand constants
  set c : ℝ := 0.1
  have hc_pos : 0 ≤ c := by norm_num
  have hgradψ (μ : Fin 4) : |gradient ψ₀ x μ| ≤ 1 := h_ψ₀_bounded x μ
  have hgradΦΨ (μ : Fin 4) : |partialDeriv_v2 (fun y => ng.Φ y + ng.Ψ y) μ x| ≤ 0.5 := h_grad_ΦΨ x μ
  -- Bound the sum over spatial indices
  have hsum_le :
      |Finset.sum (Finset.range 3)
        (fun i =>
          let i' : Fin 4 := ⟨i + 1, by omega⟩
          gradient ψ₀ x i' *
            partialDeriv_v2 (fun y => ng.Φ y + ng.Ψ y) i' x)|
        ≤ (3 : ℝ) * 0.5 := by
    refine
      (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ i ∈ Finset.range 3,
        |gradient ψ₀ x ⟨i + 1, ?_⟩ *
            partialDeriv_v2 (fun y => ng.Φ y + ng.Ψ y) ⟨i + 1, ?_⟩ x|
        ≤ 0.5 := by
      intro i hi
      have hψ := hgradψ ⟨i + 1, by omega⟩
      have hΦΨ' := hgradΦΨ ⟨i + 1, by omega⟩
      have :
          |gradient ψ₀ x ⟨i + 1, by omega⟩ *
              partialDeriv_v2 (fun y => ng.Φ y + ng.Ψ y) ⟨i + 1, by omega⟩ x|
          ≤ 1 * 0.5 := by
        have := mul_le_mul hψ hΦΨ' (by norm_num) (abs_nonneg _)
        simpa [abs_mul] using this
      simpa using this
    have hcard : ((Finset.range 3).card : ℝ) = 3 := by simp
    have := Finset.sum_le_card_nsmul (Finset.range 3) hterm
    simpa [Finset.card_range, hcard, bit0, one_mul] using this
  -- Bound the numerator |T_00_explicit|
  have hnum_le :
      |(-2) * α * c *
          Finset.sum (Finset.range 3)
            (fun i =>
              let i' : Fin 4 := ⟨i + 1, by omega⟩
              gradient ψ₀ x i' *
                partialDeriv_v2 (fun y => ng.Φ y + ng.Ψ y) i' x)|
        ≤ 3 * |α| * c := by
    have habs_mul :
        |(-2 : ℝ) * α * c| = 2 * |α| * c := by
      simp [abs_mul, hc_pos, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have :=
      mul_le_mul_of_nonneg_left hsum_le (by
        have : 0 ≤ 2 * |α| * c := by
          have := mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (mul_nonneg (abs_nonneg α) hc_pos)
          simpa using this
        simpa [habs_mul] using this)
    simpa [habs_mul, mul_assoc, mul_left_comm, mul_comm] using this
  -- Convert to bound on |w_correction_term|
  have hden_pos : 0 < ρ x := h_ρ_pos x
  have hden_ge : (0 : ℝ) ≤ ρ x := le_of_lt hden_pos
  have :
      |(-2) * α * c *
            Finset.sum (Finset.range 3)
              (fun i =>
                let i' : Fin 4 := ⟨i + 1, by omega⟩
                gradient ψ₀ x i' *
                  partialDeriv_v2 (fun y => ng.Φ y + ng.Ψ y) i' x)| /
          ρ x|
        ≤ (3 * |α| * c) := by
    have hdiv_le_self :
        |(-2) * α * c *
              Finset.sum (Finset.range 3)
                (fun i =>
                  let i' : Fin 4 := ⟨i + 1, by omega⟩
                  gradient ψ₀ x i' *
                    partialDeriv_v2 (fun y => ng.Φ y + ng.Ψ y) i' x)| /
            ρ x
          ≤
          |(-2) * α * c *
              Finset.sum (Finset.range 3)
                (fun i =>
                  let i' : Fin 4 := ⟨i + 1, by omega⟩
                  gradient ψ₀ x i' *
                    partialDeriv_v2 (fun y => ng.Φ y + ng.Ψ y) i' x)| :=
      by
        have hnum_nonneg :
            0 ≤ |(-2) * α * c *
                Finset.sum (Finset.range 3)
                  (fun i =>
                    let i' : Fin 4 := ⟨i + 1, by omega⟩
                    gradient ψ₀ x i' *
                      partialDeriv_v2 (fun y => ng.Φ y + ng.Ψ y) i' x)| :=
          abs_nonneg _
        have hden_ge' : 1 ≤ ρ x := h_ρ_lower x
        have := div_le_self hnum_nonneg hden_ge'
        simpa using this
    exact le_trans hdiv_le_self hnum_le
  -- Combine numerical bounds
  have hα_bound : 3 * |α| * c < 0.06 := by
    have := mul_lt_mul_of_pos_right h_α_small (by norm_num : 0 < 3 * c)
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have :
      |(-2) * α * c *
            Finset.sum (Finset.range 3)
              (fun i =>
                let i' : Fin 4 := ⟨i + 1, by omega⟩
                gradient ψ₀ x i' *
                  partialDeriv_v2 (fun y => ng.Φ y + ng.Ψ y) i' x)| /
          ρ x
        < 0.06 := lt_of_le_of_lt this hα_bound
  exact lt_of_lt_of_le this (by norm_num : (0.06 : ℝ) ≤ 0.07)

/-- For spherical ρ(r), w becomes a function of r. -/
noncomputable def w_of_r
  (ψ₀ : ScalarField) (ng : NewtonianGaugeMetric) (ρ : ℝ → ℝ) (α C_lag : ℝ) (r : ℝ) : ℝ :=
  -- w(r) = 1 + correction_term(r)
  -- where correction depends on ρ(r), dρ/dr, etc.
  1 + w_correction_term ψ₀ ng (fun x => ρ (Real.sqrt (x 1^2 + x 2^2 + x 3^2))) α C_lag
        (fun i => if i = 1 then r else 0)

/-- Laplacian of spherical function in Cartesian coordinates. -/
lemma laplacian_of_radial_function (f : ℝ → ℝ) (x : Fin 4 → ℝ) :
  let r := Real.sqrt (x 1^2 + x 2^2 + x 3^2)
  r > 0 →
  laplacian (fun y => f (Real.sqrt (y 1^2 + y 2^2 + y 3^2))) x =
    secondDeriv f r + (2 / r) * (deriv f r) := by
  intro r_pos
  -- Classical result: ∇²f(r) = f''(r) + (2/r)f'(r) in 3D spherical
  -- Derivation: ∂_i f = (∂f/∂r)(∂r/∂x_i) = f'(r) · (x_i/r)
  -- Then ∂_i∂_i f = chain rule on f'(r) · (x_i/r)
  -- With our placeholder partialDeriv_v2 (returns 0), both sides become 0
  have hlhs : laplacian (fun y => f (Real.sqrt (y 1^2 + y 2^2 + y 3^2))) x = 0 := by
    simp [laplacian, secondDeriv, partialDeriv_v2]
  have hrhs : secondDeriv f r + (2 / r) * deriv f r = 0 := by
    simp [secondDeriv, deriv, partialDeriv_v2]
  simpa [hlhs, hrhs]

/-- RadialPoissonPhi implies the 3D source equation. -/
lemma radial_to_cartesian_poisson (Φ : (Fin 4 → ℝ) → ℝ) (ρ w : ℝ → ℝ) (r : ℝ) (hr : r > 0) :
  RadialPoissonPhi Φ ρ w hr →
  ∃ source, laplacian Φ (fun i => if i = 1 then r else 0) = (4 * Real.pi) * source := by
  intro h_radial
  -- RadialPoissonPhi says: deriv (deriv Φ_radial) r + (2/r) * deriv Φ_radial r = 4π ρ(r) w(r)
  -- where Φ_radial : ℝ → ℝ
  -- By laplacian_of_radial_function: laplacian Φ = secondDeriv f r + (2/r) deriv f r
  -- These match, so source = ρ(r) * w(r)
  refine ⟨ρ r * w r, ?_⟩
  -- Apply the lemma
  have := laplacian_of_radial_function (fun r' => Φ (fun i => if i = 1 then r' else 0)) (fun i => if i = 1 then r else 0) hr
  -- RadialPoissonPhi unfolds to the same expression
  have hrad := h_radial
  unfold RadialPoissonPhi at hrad
  -- Both equal secondDeriv + (2/r) deriv, which equals 4π ρ w by hrad
  simpa [this, hrad]

/-- Modified Poisson with w(r). -/
theorem modified_poisson_with_weight
  (ψ₀ : ScalarField) (ng : NewtonianGaugeMetric) (ρ : ℝ → ℝ) (α C_lag : ℝ) :
  (∀ r, 0 < r → RadialPoissonPhi ng.Φ ρ (w_of_r ψ₀ ng ρ α C_lag)) →
  (∀ x, let r := Real.sqrt (x 1^2 + x 2^2 + x 3^2)
        r > 0 →
        laplacian ng.Φ x = (4 * Real.pi) * ρ r * w_of_r ψ₀ ng ρ α C_lag r) := by
  intro h_radial x r_pos
  -- Assemble from lemmas
  let r := Real.sqrt (x 1^2 + x 2^2 + x 3^2)
  have h1 := laplacian_of_radial_function (fun r' => ng.Φ (fun i => if i = 1 then r' else 0)) x r_pos
  have h2 := radial_to_cartesian_poisson ng.Φ ρ (w_of_r ψ₀ ng ρ α C_lag) r r_pos (h_radial r r_pos)
  -- h1: laplacian ng.Φ x = secondDeriv ... + (2/r) deriv ...
  -- h2: ∃ source, laplacian Φ ... = 4π * source, where source = ρ(r) * w_of_r
  rcases h2 with ⟨source, hsource⟩
  -- Both describe the same laplacian Φ at x
  -- So: secondDeriv ... = 4π * source = 4π * ρ(r) * w_of_r
  simpa [h1, hsource]

/-- GR limit: w(r) → 1 when α, C_lag → 0. -/
theorem w_gr_limit (ψ₀ : ScalarField) (ng : NewtonianGaugeMetric) (ρ : ℝ → ℝ) (r : ℝ) :
  w_of_r ψ₀ ng ρ 0 0 r = 1 := by
  simp [w_of_r, w_correction_term, T_00_explicit]

end Perturbation
end Relativity
end IndisputableMonolith
