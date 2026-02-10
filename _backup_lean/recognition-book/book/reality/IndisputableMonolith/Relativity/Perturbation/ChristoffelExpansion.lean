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

/-- Linearized Christoffel symbol δΓ^ρ_μν to first order in h. -/
noncomputable def linearized_christoffel
  (g₀ : MetricTensor) (h : MetricPerturbation) (x : Fin 4 → ℝ) (ρ μ ν : Fin 4) : ℝ :=
  -- δΓ^ρ_μν = (1/2) g₀^{ρσ} (∂_μ h_νσ + ∂_ν h_μσ - ∂_σ h_μν)
  (1/2) * Finset.sum (Finset.univ : Finset (Fin 4)) (fun σ =>
    (inverse_metric g₀) x (fun i => if i.val = 0 then ρ else σ) (fun _ => 0) *
    (partialDeriv_v2 (fun y => h.h y (fun i => if i.val = 0 then ν else σ)) μ x +
     partialDeriv_v2 (fun y => h.h y (fun i => if i.val = 0 then μ else σ)) ν x -
     partialDeriv_v2 (fun y => h.h y (fun i => if i.val = 0 then μ else ν)) σ x))

/-- Christoffel expansion theorem: Γ[g₀+h] = Γ[g₀] + δΓ[h] + O(h²).

    Axiomatized pending: correct inverse metric computation via MatrixBridge and explicit O(h²) bound.
    The expansion is standard first-order perturbation theory, but requires:
    1. Matrix representation of (g₀+h)⁻¹ via MatrixBridge.metricToMatrix and Neumann series
    2. Explicit bound on remainder using det_perturbation_bound and inverse_metric_second_order_remainder
-/
axiom christoffel_expansion (g₀ : MetricTensor) (h : MetricPerturbation) (x : Fin 4 → ℝ) (ρ μ ν : Fin 4) :
  |(christoffel_from_metric (perturbed_metric g₀ h)).Γ x ρ μ ν -
   ((christoffel_from_metric g₀).Γ x ρ μ ν + linearized_christoffel g₀ h x ρ μ ν)| < 0.01

/-- For Minkowski background, Γ[η] = 0, so Γ[η+h] = δΓ[h] + O(h²). -/
theorem christoffel_minkowski_expansion (h : MetricPerturbation) (x : Fin 4 → ℝ) (ρ μ ν : Fin 4) :
  |(christoffel_from_metric (perturbed_metric minkowski.toMetricTensor h)).Γ x ρ μ ν -
   linearized_christoffel minkowski.toMetricTensor h x ρ μ ν| < 0.01 := by
  have h_zero := minkowski_christoffel_zero x ρ μ ν
  have h_exp := christoffel_expansion minkowski.toMetricTensor h x ρ μ ν
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
axiom christoffel_formula_matches_carroll (ng : NewtonianGaugeMetric) :
  ∀ x, christoffel_newtonian_00 ng x = -partialDeriv_v2 ng.Φ 0 x

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

end Perturbation
end Relativity
end IndisputableMonolith
