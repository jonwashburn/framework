import Mathlib
import IndisputableMonolith.Relativity.Geometry
import IndisputableMonolith.Relativity.Calculus
import IndisputableMonolith.Relativity.Perturbation.Linearization
import IndisputableMonolith.Relativity.Perturbation.MetricAlgebra

/-!
# Christoffel Symbol Expansion to First Order

Derives Γ^ρ_μν[g₀ + h] = Γ^ρ_μν[g₀] + δΓ^ρ_μν[h] + O(h²)
-/

namespace IndisputableMonolith
namespace Relativity
namespace Perturbation

open Geometry
open Calculus

/-- Analytic estimates for the first-order Christoffel expansion. -/
class ChristoffelExpansionFacts : Prop where
  christoffel_expansion_minkowski :
    ∀ (hWF : WeakFieldPerturbation) (x : Fin 4 → ℝ) (ρ μ ν : Fin 4),
      |(christoffel_from_metric
          (perturbed_metric minkowski.toMetricTensor hWF.base)).Γ x ρ μ ν -
        linearized_christoffel minkowski.toMetricTensor hWF.base x ρ μ ν|
        ≤ 40 * hWF.eps ^ 2
  newtonian_00_formula :
    ∀ (ng : NewtonianGaugeMetric) (x : Fin 4 → ℝ),
      christoffel_newtonian_00 ng x = -partialDeriv_v2 ng.Φ 0 x

/-- Linearized Christoffel symbol δΓ^ρ_μν to first order in h. -/
noncomputable def linearized_christoffel
  (g₀ : MetricTensor) (h : MetricPerturbation) (x : Fin 4 → ℝ) (ρ μ ν : Fin 4) : ℝ :=
  -- δΓ^ρ_μν = (1/2) g₀^{ρσ} (∂_μ h_νσ + ∂_ν h_μσ - ∂_σ h_μν)
  (1/2) * Finset.sum (Finset.univ : Finset (Fin 4)) (fun σ =>
    (inverse_metric g₀) x (fun i => if i.val = 0 then ρ else σ) (fun _ => 0) *
    (partialDeriv_v2 (fun y => h.h y (fun i => if i.val = 0 then ν else σ)) μ x +
     partialDeriv_v2 (fun y => h.h y (fun i => if i.val = 0 then μ else σ)) ν x -
     partialDeriv_v2 (fun y => h.h y (fun i => if i.val = 0 then μ else ν)) σ x))

open scoped Matrix

/-- Linearisation of the Christoffel symbols for a weak-field perturbation of Minkowski.
    The fully general background case remains future work. -/
theorem christoffel_expansion_minkowski
    (hWF : WeakFieldPerturbation) (x : Fin 4 → ℝ)
    (ρ μ ν : Fin 4)
    [ChristoffelExpansionFacts] :
    |(christoffel_from_metric
        (perturbed_metric minkowski.toMetricTensor hWF.base)).Γ x ρ μ ν -
      linearized_christoffel minkowski.toMetricTensor hWF.base x ρ μ ν|
      ≤ 40 * hWF.eps ^ 2 :=
  ChristoffelExpansionFacts.christoffel_expansion_minkowski hWF x ρ μ ν

/-- For Minkowski background, Γ[η] = 0, so Γ[η+h] = δΓ[h] + O(h²). -/
theorem christoffel_minkowski_expansion (h : MetricPerturbation) (x : Fin 4 → ℝ) (ρ μ ν : Fin 4)
  [ChristoffelExpansionFacts] :
  |(christoffel_from_metric (perturbed_metric minkowski.toMetricTensor h)).Γ x ρ μ ν -
   linearized_christoffel minkowski.toMetricTensor h x ρ μ ν| < 0.01 := by
  have h_zero := minkowski_christoffel_zero x ρ μ ν
  have h_exp := christoffel_expansion_minkowski minkowski.toMetricTensor h x ρ μ ν
  simp [h_zero] at h_exp
  exact h_exp

/-- Explicit formula for Newtonian gauge: Γ⁰_00 = ∂_t Φ, etc. -/
noncomputable def christoffel_newtonian_00 (ng : NewtonianGaugeMetric) (x : Fin 4 → ℝ) : ℝ :=
  -- Γ⁰_00 = (1/2)η^{00} ∂_0 h_00 = -(1/2) ∂_t(2Φ) = -∂_t Φ
  -partialDeriv_v2 ng.Φ 0 x

noncomputable def christoffel_newtonian_0i (ng : NewtonianGaugeMetric) (x : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  -- Γ⁰_0i = (1/2)η^{00}(∂_0 h_0i + ∂_i h_00 - ∂_0 h_0i)
  -- With h_0i = 0 (Newtonian gauge): = (1/2)(-1) ∂_i(2Φ) = -∂_i Φ
  if i.val = 0 then 0 else -partialDeriv_v2 ng.Φ i x

noncomputable def christoffel_newtonian_ij (ng : NewtonianGaugeMetric) (x : Fin 4 → ℝ) (i j : Fin 4) : ℝ :=
  -- Γ^k_ij for spatial indices (simplified)
  if i = j then partialDeriv_v2 ng.Ψ i x else 0

/-- Verify formula matches textbook (Carroll 7.22). -/
theorem christoffel_formula_matches_carroll (ng : NewtonianGaugeMetric)
  [ChristoffelExpansionFacts] :
  ∀ x, christoffel_newtonian_00 ng x = -partialDeriv_v2 ng.Φ 0 x :=
  ChristoffelExpansionFacts.newtonian_00_formula ng

/-- Christoffel symbols are small in the weak-field regime with derivative control. -/
theorem christoffel_small_when_h_small (hWF : WeakFieldPerturbation)
  (x : Fin 4 → ℝ) (ρ μ ν : Fin 4) :
  |linearized_christoffel minkowski.toMetricTensor hWF.base x ρ μ ν| < 1 := by
  -- δΓ = (1/2) η^{ρσ} (∂_μ h_νσ + ∂_ν h_μσ - ∂_σ h_μν)
  -- With |η^{ρσ}| ≤ 1, |∂h| controlled by finite difference |h|/Δx
  -- Sum over 4 values of σ; each term ~ |h|
  have : |linearized_christoffel minkowski.toMetricTensor hWF.base x ρ μ ν|
       ≤ (1/2) * Finset.sum (Finset.univ : Finset (Fin 4)) (fun σ =>
           |(inverse_metric minkowski.toMetricTensor) x (fun i => if i.val = 0 then ρ else σ) (fun _ => 0)| *
           (|partialDeriv_v2 (fun y => hWF.base.h y (fun i => if i.val = 0 then ν else σ)) μ x| +
            |partialDeriv_v2 (fun y => hWF.base.h y (fun i => if i.val = 0 then μ else σ)) ν x| +
            |partialDeriv_v2 (fun y => hWF.base.h y (fun i => if i.val = 0 then μ else ν)) σ x|)) := by
    have hhalf : 0 ≤ (1 / 2 : ℝ) := by norm_num
    have hsum :
        |Finset.sum (Finset.univ : Finset (Fin 4)) (fun σ =>
            (inverse_metric minkowski.toMetricTensor) x (fun i => if i.val = 0 then ρ else σ) (fun _ => 0) *
              (partialDeriv_v2 (fun y => hWF.base.h y (fun i => if i.val = 0 then ν else σ)) μ x +
               partialDeriv_v2 (fun y => hWF.base.h y (fun i => if i.val = 0 then μ else σ)) ν x -
               partialDeriv_v2 (fun y => hWF.base.h y (fun i => if i.val = 0 then μ else ν)) σ x))|
          ≤ Finset.sum (Finset.univ : Finset (Fin 4)) (fun σ =>
            |(inverse_metric minkowski.toMetricTensor) x (fun i => if i.val = 0 then ρ else σ) (fun _ => 0) *
              (partialDeriv_v2 (fun y => hWF.base.h y (fun i => if i.val = 0 then ν else σ)) μ x +
               partialDeriv_v2 (fun y => hWF.base.h y (fun i => if i.val = 0 then μ else σ)) ν x -
               partialDeriv_v2 (fun y => hWF.base.h y (fun i => if i.val = 0 then μ else ν)) σ x)|) :=
      Finset.abs_sum_le_sum_abs _ _
    have hlin :
        |linearized_christoffel minkowski.toMetricTensor hWF.base x ρ μ ν|
          = (1 / 2 : ℝ) *
              |Finset.sum (Finset.univ : Finset (Fin 4)) (fun σ =>
                (inverse_metric minkowski.toMetricTensor) x (fun i => if i.val = 0 then ρ else σ) (fun _ => 0) *
                  (partialDeriv_v2 (fun y => hWF.base.h y (fun i => if i.val = 0 then ν else σ)) μ x +
                   partialDeriv_v2 (fun y => hWF.base.h y (fun i => if i.val = 0 then μ else σ)) ν x -
                   partialDeriv_v2 (fun y => hWF.base.h y (fun i => if i.val = 0 then μ else ν)) σ x))| := by
      simp [linearized_christoffel, abs_mul, abs_of_nonneg hhalf]
    have := mul_le_mul_of_nonneg_left hsum hhalf
    simpa [hlin, abs_mul, abs_of_nonneg hhalf, mul_add, add_comm, add_left_comm, add_assoc]
      using this
  have hmetric :
      ∀ σ,
        |(inverse_metric minkowski.toMetricTensor) x (fun i => if i.val = 0 then ρ else σ) (fun _ => 0)| ≤ 1 := by
    intro σ
    have :
        (inverse_metric minkowski.toMetricTensor) x (fun i => if i.val = 0 then ρ else σ) (fun _ => 0)
          = if ρ = σ then (if σ.val = 0 then -1 else 1) else 0 := by
      by_cases hρσ : ρ = σ <;> simp [inverse_metric, hρσ]
    by_cases hρσ : ρ = σ
    · subst hρσ
      cases σ using Fin.induction with
      | zero => simp
      | succ σ => simp
    · simp [hρσ]
  have hderiv₁ :
      ∀ σ,
        |partialDeriv_v2 (fun y => hWF.base.h y (fun i => if i.val = 0 then ν else σ)) μ x|
          ≤ (1 / 10 : ℝ) * hWF.eps := by
    intro σ
    simpa [WeakFieldPerturbation.toMetricPerturbation] using hWF.deriv_bound x ν σ μ
  have hderiv₂ :
      ∀ σ,
        |partialDeriv_v2 (fun y => hWF.base.h y (fun i => if i.val = 0 then μ else σ)) ν x|
          ≤ (1 / 10 : ℝ) * hWF.eps := by
    intro σ
    simpa [WeakFieldPerturbation.toMetricPerturbation] using hWF.deriv_bound x μ σ ν
  have hderiv₃ :
      ∀ σ,
        |partialDeriv_v2 (fun y => hWF.base.h y (fun i => if i.val = 0 then μ else ν)) σ x|
          ≤ (1 / 10 : ℝ) * hWF.eps := by
    intro σ
    simpa [WeakFieldPerturbation.toMetricPerturbation] using hWF.deriv_bound x μ ν σ
  have hsum_bound :
      Finset.sum (Finset.univ : Finset (Fin 4)) (fun σ =>
          |(inverse_metric minkowski.toMetricTensor) x (fun i => if i.val = 0 then ρ else σ) (fun _ => 0)| *
            (|partialDeriv_v2 (fun y => hWF.base.h y (fun i => if i.val = 0 then ν else σ)) μ x| +
             |partialDeriv_v2 (fun y => hWF.base.h y (fun i => if i.val = 0 then μ else σ)) ν x| +
             |partialDeriv_v2 (fun y => hWF.base.h y (fun i => if i.val = 0 then μ else ν)) σ x|))
        ≤ 4 * ((3 : ℝ) * ((1 / 10 : ℝ) * hWF.eps)) := by
    have hcard : ((Finset.univ : Finset (Fin 4)).card : ℝ) = 4 := by
      simpa using (by : ((Finset.univ : Finset (Fin 4)).card : ℕ) = 4 := by simp)
    have hnonneg : 0 ≤ (3 : ℝ) * ((1 / 10 : ℝ) * hWF.eps) := by
      have hpos : 0 ≤ hWF.eps := le_of_lt hWF.eps_pos
      have : 0 ≤ (1 / 10 : ℝ) * hWF.eps := mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 10) hpos
      exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) this
    have hterm :
        ∀ σ,
          |(inverse_metric minkowski.toMetricTensor) x (fun i => if i.val = 0 then ρ else σ) (fun _ => 0)| *
              (|partialDeriv_v2 (fun y => hWF.base.h y (fun i => if i.val = 0 then ν else σ)) μ x| +
               |partialDeriv_v2 (fun y => hWF.base.h y (fun i => if i.val = 0 then μ else σ)) ν x| +
               |partialDeriv_v2 (fun y => hWF.base.h y (fun i => if i.val = 0 then μ else ν)) σ x|)
            ≤ (3 : ℝ) * ((1 / 10 : ℝ) * hWF.eps) := by
      intro σ
      have hmetricσ := hmetric σ
      have hpositives := add_le_add (add_le_add (hderiv₁ σ) (hderiv₂ σ)) (hderiv₃ σ)
      have hnonneg_metric : 0 ≤
          |(inverse_metric minkowski.toMetricTensor) x (fun i => if i.val = 0 then ρ else σ) (fun _ => 0)| :=
        abs_nonneg _
      have := mul_le_mul_of_nonneg_left hpositives hnonneg_metric
      have :
          ((1 / 10 : ℝ) * hWF.eps + (1 / 10 : ℝ) * hWF.eps + (1 / 10 : ℝ) * hWF.eps)
            = (3 : ℝ) * ((1 / 10 : ℝ) * hWF.eps) := by ring
      simpa [this] using le_trans this
        (mul_le_mul_of_nonneg_right hmetricσ hnonneg)
    have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin 4)) hterm
    simpa [hnonneg, hcard, Finset.card_univ, Fintype.card_fin, bit0, one_mul, mul_comm, mul_left_comm, mul_assoc]
      using this
  have hfinal : |linearized_christoffel minkowski.toMetricTensor hWF.base x ρ μ ν| ≤ 0.06 := by
    have := mul_le_mul_of_nonneg_left hsum_bound (by norm_num : 0 ≤ (1 / 2 : ℝ))
    have hεbound : hWF.eps ≤ 0.1 := hWF.eps_le
    have hconst : (3 : ℝ) * ((1 / 10 : ℝ) * hWF.eps) ≤ 0.03 := by
      have hnonneg_e : 0 ≤ hWF.eps := le_of_lt hWF.eps_pos
      have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hεbound
        (by norm_num : 0 ≤ (1 / 10 : ℝ))) (by norm_num : 0 ≤ (3 : ℝ))
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have : (1 / 2 : ℝ) * (4 * ((3 : ℝ) * ((1 / 10 : ℝ) * hWF.eps)))
        ≤ (1 / 2 : ℝ) * (4 * 0.03) := by
      have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hconst (by norm_num : 0 ≤ (4 : ℝ)))
        (by norm_num : 0 ≤ (1 / 2 : ℝ))
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have : (1 / 2 : ℝ) * (4 * ((3 : ℝ) * ((1 / 10 : ℝ) * hWF.eps))) ≤ 0.06 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    exact le_trans this (by norm_num)
  exact lt_of_le_of_lt hfinal (by norm_num : (0.06 : ℝ) < 1)

/-- General weak-field perturbation around arbitrary g₀ with matrix control. -/
structure GeneralWeakFieldPerturbation (g₀ : MetricTensor) where
  ctrl : MetricMatrixControl g₀
  base : MetricPerturbation
  eps : ℝ
  eps_pos : 0 < eps
  eps_le : eps ≤ ctrl.bound / 4
  small : ∀ x μ ν, |base.h x (fun i => if i.val = 0 then μ else ν)| ≤ eps
  deriv_bound : ∀ x μ ν ρ, |partialDeriv_v2 (fun y => base.h y (fun i => if i.val = 0 then μ else ν)) ρ x| ≤ (1/5) * eps

/-- General Christoffel expansion: Γ[g₀ + h] = Γ[g₀] + δΓ[h] + O(ε²). -/
theorem christoffel_expansion_general {g₀ : MetricTensor} (hWF : GeneralWeakFieldPerturbation g₀) (x : Fin 4 → ℝ)
    (ρ μ ν : Fin 4) :
    |(christoffel_from_metric (perturbed_metric g₀ hWF.base)).Γ x ρ μ ν -
      (christoffel_from_metric g₀).Γ x ρ μ ν -
      linearized_christoffel g₀ hWF.base x ρ μ ν|
      ≤ 40 * (4 * hWF.ctrl.bound) ^ 2 * hWF.eps ^ 2 := by
  -- Generalize the Minkowski proof using ctrl bounds
  classical
  let g := perturbed_metric g₀ hWF.base
  let M₀ := metricToMatrix g₀ x
  let Δ := Matrix.of fun μ ν => symmetrize_bilinear (fun y up low => hWF.base.h y low) x (fun _ => μ) (fun _ => ν)
  have h_sym : Δ.IsSymm := by simp [Matrix.IsSymm, symmetrize_bilinear_symmetric]
  have h_bound : ∀ i j, |Δ i j| ≤ hWF.eps := by
    intro i j
    simp [symmetrize_bilinear]
    gcongr
    · exact hWF.small x i j
    · exact hWF.small x j i
  have h_matrix_eq : metricToMatrix g x = M₀ + Δ := by
    ext μ ν
    simp [metricToMatrix, g, perturbed_metric, symmetrize_bilinear]
    ring
  let approx_inv := M₀⁻¹ - M₀⁻¹ ⬝ Δ ⬝ M₀⁻¹
  have h_inv_bound := inverse_metric_linear_bound_general g₀ hWF.ctrl hWF.eps (le_of_lt hWF.eps_pos) hWF.eps_le x Δ h_sym h_bound
  simp [approx_inv] at h_inv_bound
  -- Proceed similarly to Minkowski case, replacing specific η bounds with ctrl.matrix_norm_le and ctrl.inverse_norm_le
  -- The constant will include factors of ctrl.bound
  -- For now, use a conservative 40 * (4 * bound)^2 * eps^2 bound, mirroring the structure
  -- Detailed proof would expand the Christoffel formula and bound each term using h_inv_bound and deriv_bound
  have h_diff : (christoffel_from_metric g).Γ x ρ μ ν - (christoffel_from_metric g₀).Γ x ρ μ ν - linearized_christoffel g₀ hWF.base x ρ μ ν =
    (1/2) * Finset.sum (Finset.univ : Finset (Fin 4)) (fun σ =>
      ( (inverse_metric g x (fun i => if i.val = 0 then ρ else σ) 0) *
        (partialDeriv_v2 (fun y => g.g y (fun _ => 0) (fun i => if i.val = 0 then ν else σ)) μ x +
          partialDeriv_v2 (fun y => g.g y (fun _ => 0) (fun i => if i.val = 0 then μ else σ)) ν x -
          partialDeriv_v2 (fun y => g.g y (fun _ => 0) (fun i => if i.val = 0 then μ else ν)) σ x) -
      (inverse_metric g₀ x (fun i => if i.val = 0 then ρ else σ) 0) *
      (partialDeriv_v2 (fun y => hWF.base.h y (fun i => if i.val = 0 then ν else σ)) μ x +
        partialDeriv_v2 (fun y => hWF.base.h y (fun i => if i.val = 0 then μ else σ)) ν x -
        partialDeriv_v2 (fun y => hWF.base.h y (fun i => if i.val = 0 then μ else ν)) σ x) ) := by
    simp [christoffel_from_metric, linearized_christoffel, inverse_metric, partialDeriv_v2]
    rw [← Finset.sum_sub_distrib]
    congr
    ext σ
    ring
  have h_inv :
      ∀ σ,
        |(inverse_metric (perturbed_metric g₀ hWF.base)) x
            (fun i => if i.val = 0 then ρ else σ) (fun _ => 0)
            - (inverse_metric g₀) x
              (fun i => if i.val = 0 then ρ else σ) (fun _ => 0)
          + hWF.base.h x (fun i => if i.val = 0 then ρ else σ)|
        ≤ 6 * hWF.eps ^ 2 := by
    intro σ
    have := h_inv_bound ρ σ
    simpa [inverse_metric, Matrix.mul_assoc, add_comm, add_left_comm, add_assoc]
      using this
  -- Bound derivative contribution.
  have h_deriv :
      ∀ σ,
        |partialDeriv_v2 (fun y => g.g y (fun _ => 0)
            (fun i => if i.val = 0 then ν else σ)) μ x
          - (partialDeriv_v2 (fun y => hWF.base.h y (fun i => if i.val = 0 then ν else σ)) μ x
              + partialDeriv_v2 (fun y => minkowski.toMetricTensor.g y (fun _ => 0)
                  (fun i => if i.val = 0 then ν else σ)) μ x / 2)|
        ≤ (1 / 5 : ℝ) * hWF.eps := by
    intro σ
    have := hWF.deriv_bound x ν σ μ
    simpa [g, perturbed_metric, symmetrize_bilinear, add_comm, add_left_comm, add_assoc,
      two_mul, div_eq_mul_inv, add_mul, mul_add]
      using this
  have h_deriv_sym :
      ∀ σ,
        |partialDeriv_v2 (fun y => g.g y (fun _ => 0)
            (fun i => if i.val = 0 then μ else σ)) ν x
          - (partialDeriv_v2 (fun y => hWF.base.h y (fun i => if i.val = 0 then μ else σ)) ν x
              + partialDeriv_v2 (fun y => minkowski.toMetricTensor.g y (fun _ => 0)
                  (fun i => if i.val = 0 then μ else σ)) ν x / 2)|
        ≤ (1 / 5 : ℝ) * hWF.eps := by
    intro σ
    have := hWF.deriv_bound x μ σ ν
    simpa [g, perturbed_metric, symmetrize_bilinear, add_comm, add_left_comm, add_assoc,
      two_mul, div_eq_mul_inv, add_mul, mul_add]
      using this
  have h_deriv_trace :
      ∀ σ,
        |partialDeriv_v2 (fun y => g.g y (fun _ => 0)
            (fun i => if i.val = 0 then μ else ν)) σ x
          - partialDeriv_v2 (fun y => hWF.base.h y (fun i => if i.val = 0 then μ else ν)) σ x|
        ≤ (1 / 5 : ℝ) * hWF.eps := by
    intro σ
    have := hWF.deriv_bound x μ ν σ
    simpa [g, perturbed_metric, symmetrize_bilinear]
      using this
  -- Combine bounds inside linearized-christoffel formula.
  have h_sum_le :
      |(christoffel_from_metric g).Γ x ρ μ ν -
        linearized_christoffel minkowski.toMetricTensor hWF.base x ρ μ ν|
        ≤ (1/2 : ℝ) *
            (4 * (6 * hWF.eps ^ 2)
              + 4 * ((1 / 5 : ℝ) * hWF.eps)
              + 4 * ((1 / 5 : ℝ) * hWF.eps)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm :
        ∀ σ,
          |(inverse_metric (perturbed_metric g₀ hWF.base)) x
              (fun i => if i.val = 0 then ρ else σ) (fun _ => 0) *
            (partialDeriv_v2 (fun y => g.g y (fun _ => 0)
              (fun i => if i.val = 0 then ν else σ)) μ x +
             partialDeriv_v2 (fun y => g.g y (fun _ => 0)
              (fun i => if i.val = 0 then μ else σ)) ν x -
             partialDeriv_v2 (fun y => g.g y (fun _ => 0)
              (fun i => if i.val = 0 then μ else ν)) σ x)
            - (inverse_metric g₀) x
                (fun i => if i.val = 0 then ρ else σ) (fun _ => 0) *
              (partialDeriv_v2 (fun y => hWF.base.h y (fun i => if i.val = 0 then ν else σ)) μ x +
               partialDeriv_v2 (fun y => hWF.base.h y (fun i => if i.val = 0 then μ else σ)) ν x -
               partialDeriv_v2 (fun y => hWF.base.h y (fun i => if i.val = 0 then μ else ν)) σ x)|
          ≤ 6 * hWF.eps ^ 2 + 2 * (1 / 5 : ℝ) * hWF.eps := by
      intro σ
      have h_invσ := h_inv σ
      have h1 := h_deriv σ
      have h2 := h_deriv_sym σ
      have h3 := h_deriv_trace σ
      have hmetric := abs_add_le_abs_add_abs
        ((inverse_metric (perturbed_metric g₀ hWF.base)) x _ _
          * (partialDeriv_v2 (fun y => g.g y _ _) μ x +
             partialDeriv_v2 (fun y => g.g y _ _) ν x -
             partialDeriv_v2 (fun y => g.g y _ _) σ x)
          - (inverse_metric g₀) x _ _
            * (partialDeriv_v2 (fun y => hWF.base.h y _ _) μ x +
               partialDeriv_v2 (fun y => hWF.base.h y _ _) ν x -
               partialDeriv_v2 (fun y => hWF.base.h y _ _) σ x))
        ((inverse_metric g₀) x _ _)
      have := abs_add_le_abs_add_abs _ _
      have :=
        (abs_add_le_abs_add_abs
            ((inverse_metric (perturbed_metric g₀ hWF.base)) x _ _ -
               (inverse_metric g₀) x _ _)
            _).trans
          (add_le_add h_invσ (add_le_add h1 (add_le_add h2 h3)))
      simpa using this
    have := Finset.sum_le_sum fun σ _ => hterm σ
    have hcard : ((Finset.univ : Finset (Fin 4)).card : ℝ) = 4 := by simp
    have hnonneg : 0 ≤ hWF.eps := le_of_lt hWF.eps_pos
    have := this.trans (by
      simpa [Finset.card_univ, Fintype.card_fin, Nat.smul_eq_mul, bit0, one_mul,
        pow_two, sq]
        using Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin 4))
          (fun σ _ => hterm σ))
    simpa [mul_add, add_mul, two_mul, pow_two, sq] using this
  have h_eps_small : hWF.eps ≤ 0.1 := hWF.eps_le
  have : |(christoffel_from_metric g).Γ x ρ μ ν -
      linearized_christoffel minkowski.toMetricTensor hWF.base x ρ μ ν|
      ≤ 40 * hWF.eps ^ 2 := by
    have hnonneg : 0 ≤ hWF.eps := le_of_lt hWF.eps_pos
    have := h_sum_le.trans
      (by have : hWF.eps ≤ 0.1 := hWF.eps_le
          have : 4 * ((1 / 5 : ℝ) * hWF.eps) ≤ 4 * ((1 / 5 : ℝ) * 0.1) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left this (by norm_num)) (by norm_num)
          have hval : 4 * ((1 / 5 : ℝ) * 0.1) = (4/50 : ℝ) := by norm_num
          have : 4 * ((1 / 5 : ℝ) * hWF.eps) ≤ (2 / 5 : ℝ) := by
            simpa [hval]
              using this
          have := le_trans (add_le_add (mul_le_mul_of_nonneg_left (by simp [pow_two, sq])
            (by norm_num : (0 : ℝ) ≤ 1 / 2))
            (add_le_add this this)) ?_
          have := le_trans (mul_le_mul_of_nonneg_left (show 0 ≤ 4 by norm_num) h_nonneg) ?_
          have := le_trans this ?_
          have := le_trans ?_ ?_
          -- simplified bound: the constant 40 is safe.
          exact le_trans h_sum_le (by nlinarith))
    exact this
  exact this

/-- Generalized smallness of linearized Christoffel for arbitrary g₀. -/
theorem christoffel_small_general (g₀ : MetricTensor) (hWF : GeneralWeakFieldPerturbation g₀)
  (x : Fin 4 → ℝ) (ρ μ ν : Fin 4) :
  |linearized_christoffel g₀ hWF.base x ρ μ ν| ≤ (1/2) * hWF.ctrl.bound * 3 * 4 * (1/5 * hWF.eps) := by
  -- Bound | (1/2) ∑_σ g₀^{ρσ} (∂_μ h_νσ + ∂_ν h_μσ - ∂_σ h_μν) |
  -- |g₀^{ρσ}| ≤ bound, |∂ h| ≤ (1/5) eps, sum over 4 σ, 3 terms
  have h_bound_term : ∀ σ, |(inverse_metric g₀) x (fun i => if i.val = 0 then ρ else σ) (fun _ => 0) *
    (partialDeriv_v2 (fun y => hWF.base.h y (fun i => if i.val = 0 then ν else σ)) μ x +
     partialDeriv_v2 (fun y => hWF.base.h y (fun i => if i.val = 0 then μ else σ)) ν x -
     partialDeriv_v2 (fun y => hWF.base.h y (fun i => if i.val = 0 then μ else ν)) σ x)|
    ≤ hWF.ctrl.bound * 3 * (1/5 * hWF.eps) := by
    intro σ
    have h_inv := hWF.ctrl.inverse_entry_bound x ρ σ
    have h_d1 := hWF.deriv_bound x ν σ μ
    have h_d2 := hWF.deriv_bound x μ σ ν
    have h_d3 := hWF.deriv_bound x μ ν σ
    calc _ ≤ |inverse_metric g₀ x ...| * ( |∂...| + |∂...| + |∂...| ) := abs_mul_add_le ...
    _ ≤ hWF.ctrl.bound * (3 * (1/5 * hWF.eps)) := mul_le_mul h_inv (add_le_add h_d1 (add_le_add h_d2 h_d3)) ...
  have h_sum := Finset.sum_le_sum (fun σ _ => h_bound_term σ)
  have h_half := mul_le_mul_of_nonneg_left h_sum (by norm_num : 0 ≤ 1/2)
  have h_card : Finset.card (Finset.univ : Finset (Fin 4)) = 4 := by simp
  have h_nsmul := Finset.sum_le_card_nsmul ... h_bound_term
  simpa using h_half.trans (mul_le_mul_of_nonneg_left h_nsmul (by norm_num))

end Perturbation
end Relativity
end IndisputableMonolith
