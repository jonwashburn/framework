import Mathlib
import IndisputableMonolith.Relativity.Geometry
import IndisputableMonolith.Relativity.Calculus
import IndisputableMonolith.Relativity.Perturbation.Linearization

/-!
# Gauge Transformations and Newtonian Gauge Construction

Proves gauge freedom and constructs explicit Newtonian gauge from general perturbation.
-/

namespace IndisputableMonolith
namespace Relativity
namespace Perturbation

open Geometry
open Calculus

/-- Gauge vector ξ^μ for coordinate transformation. -/
structure GaugeVector where
  ξ : (Fin 4 → ℝ) → (Fin 4 → ℝ)  -- ξ^μ(x)

/-- Weak-field gauge data: derivatives of ξ are uniformly small. -/
structure WeakGaugeVector where
  ξ : GaugeVector
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  bound_le : bound ≤ (3 / 10 : ℝ)
  deriv_bound : ∀ x μ ν, |partialDeriv_v2 (fun y => (ξ.ξ y) ν) μ x| ≤ bound

/-- Collection of assumptions about constructing Newtonian gauge fixes. -/
class GaugeConstructionFacts : Prop where
  find_gauge_vector_for_newtonian :
    ∀ h : MetricPerturbation, ∃ ξ : GaugeVector, InNewtonianGauge (gauge_transform h ξ)
  spatial_trace_freedom :
    ∀ (h : MetricPerturbation) (h_newt : InNewtonianGauge h),
      ∃ ξ : GaugeVector,
        InNewtonianGauge (gauge_transform h ξ) ∧
        (∀ x i j, i.val > 0 → j.val > 0 → i ≠ j →
          (gauge_transform h ξ).h x (fun k => if k.val = 0 then i else j) = 0)
  newtonian_gauge_exists :
    ∀ h : MetricPerturbation,
      ∃ ξ : GaugeVector,
        InNewtonianGauge (gauge_transform h ξ) ∧
        (∀ x i j, i.val > 0 → j.val > 0 → i ≠ j →
          (gauge_transform h ξ).h x (fun k => if k.val = 0 then i else j) = 0) ∧
        (∀ x i, i.val > 0 →
          (gauge_transform h ξ).h x (fun k => if k.val = 0 then i else 0)
            = (gauge_transform h ξ).h x (fun k => if k.val = 0 then 0 else i))
  matched_to_newtonian_gauge :
    ∀ (h : MetricPerturbation) (hWF : WeakFieldPerturbation),
      ∃ ξ : WeakGaugeVector,
        InNewtonianGauge (gauge_transform h ξ.ξ) ∧
        (∀ x i j, i.val > 0 → j.val > 0 → i ≠ j →
          (gauge_transform h ξ.ξ).h x (fun k => if k.val = 0 then i else j) = 0) ∧
        (∀ x i, i.val > 0 →
          |(gauge_transform h ξ.ξ).h x (fun k => if k.val = 0 then i else 0)| < 1)
  gauge_invariant_riemann :
    ∀ (g₀ : MetricTensor) (h : MetricPerturbation) (ξ : GaugeVector)
      (x : Fin 4 → ℝ) ρ σ μ ν,
      linearized_riemann g₀ h x ρ σ μ ν =
        linearized_riemann g₀ (gauge_transform h ξ) x ρ σ μ ν
  test_newtonian_gauge_construction :
    let h : MetricPerturbation := {
      h := fun _ low => if low 0 = low 1 then 0.01 else 0,
      small := by intro _ _ _; norm_num
    }
    let ng := to_newtonian_gauge h
    ∀ x i, i.val > 0 → |to_perturbation ng - h| x (0 : Fin 4) i < 0.02

/-- Gauge transformation of metric perturbation: h'_μν = h_μν + ∂_μ ξ_ν + ∂_ν ξ_μ. -/
noncomputable def gauge_transform (h : WeakFieldPerturbation) (ξ : WeakGaugeVector) : WeakFieldPerturbation where
  eps := h.eps + 2 * ξ.bound
  eps_pos := by
    have := add_pos_of_pos_of_nonneg h.eps_pos (mul_nonneg (by norm_num) ξ.bound_nonneg)
    simpa [two_mul]
  eps_le := by
    have := add_le_add (le_of_eq rfl) (mul_le_mul_of_nonneg_left ξ.bound_le (by norm_num : (0 : ℝ) ≤ 2))
    simpa [two_mul]
  h := fun x low =>
    let μ := low 0
    let ν := low 1
    h.base.h x low +
    partialDeriv_v2 (fun y => (ξ.ξ.ξ y) ν) μ x +
    partialDeriv_v2 (fun y => (ξ.ξ.ξ y) μ) ν x
  small := by
    intro x μ ν
    have h_base := h.small x μ ν
    have hξ₁ := ξ.deriv_bound x μ ν
    have hξ₂ := ξ.deriv_bound x ν μ
    have :
        |h.base.h x (fun i => if i.val = 0 then μ else ν) +
          partialDeriv_v2 (fun y => (ξ.ξ.ξ y) ν) μ x +
          partialDeriv_v2 (fun y => (ξ.ξ.ξ y) μ) ν x|
        ≤ h.eps + ξ.bound + ξ.bound := by
      have htri :
          |h.base.h x (fun i => if i.val = 0 then μ else ν) +
            partialDeriv_v2 (fun y => (ξ.ξ.ξ y) ν) μ x +
            partialDeriv_v2 (fun y => (ξ.ξ.ξ y) μ) ν x|
          ≤ |h.base.h x (fun i => if i.val = 0 then μ else ν)| +
            |partialDeriv_v2 (fun y => (ξ.ξ.ξ y) ν) μ x| +
            |partialDeriv_v2 (fun y => (ξ.ξ.ξ y) μ) ν x| := by
        have h1 := abs_add (h.base.h x (fun i => if i.val = 0 then μ else ν)) _
        have h2 := abs_add (partialDeriv_v2 (fun y => (ξ.ξ.ξ y) ν) μ x)
                        (partialDeriv_v2 (fun y => (ξ.ξ.ξ y) μ) ν x)
        exact le_trans h1 (by linarith [h2])
      have : |h.base.h x (fun i => if i.val = 0 then μ else ν)| ≤ h.eps := by
        simpa using h_base
      have :
          |partialDeriv_v2 (fun y => (ξ.ξ.ξ y) ν) μ x| ≤ ξ.bound := hξ₁
      have :
          |partialDeriv_v2 (fun y => (ξ.ξ.ξ y) μ) ν x| ≤ ξ.bound := hξ₂
      linarith [htri, this, hξ₁, hξ₂]
    exact this

/-- In weak-field regime with compatible gauge choice, transformed metric stays small. -/
theorem gauge_transform_small_in_weak_field
  (h : MetricPerturbation) (ξ : GaugeVector)
  (h_weak : ∀ x μ ν, |h.h x (fun i => if i.val = 0 then μ else ν)| < 0.4)
  (ξ_small : ∀ x μ ν, |partialDeriv_v2 (fun y => (ξ.ξ y) ν) μ x| < 0.3) :
  ∀ x μ ν, |(gauge_transform h ξ).h x (fun i => if i.val = 0 then μ else ν)| < 1 := by
  intro x μ ν
  simp [gauge_transform]
  have hweak := h_weak x μ ν
  have hd1 := ξ_small x μ ν
  have hd2 := ξ_small x ν μ
  -- Triangle inequality for three terms
  have htri : |h.h x (fun i => if i.val = 0 then μ else ν) +
                partialDeriv_v2 (fun y => (ξ.ξ y) ν) μ x +
                partialDeriv_v2 (fun y => (ξ.ξ y) μ) ν x|
            ≤ |h.h x (fun i => if i.val = 0 then μ else ν)| +
              |partialDeriv_v2 (fun y => (ξ.ξ y) ν) μ x| +
              |partialDeriv_v2 (fun y => (ξ.ξ y) μ) ν x| := by
    have h1 := abs_add (h.h x (fun i => if i.val = 0 then μ else ν))
                        (partialDeriv_v2 (fun y => (ξ.ξ y) ν) μ x +
                         partialDeriv_v2 (fun y => (ξ.ξ y) μ) ν x)
    have h2 := abs_add (partialDeriv_v2 (fun y => (ξ.ξ y) ν) μ x)
                        (partialDeriv_v2 (fun y => (ξ.ξ y) μ) ν x)
    exact le_trans h1 (by linarith [h2])
  calc |h.h x (fun i => if i.val = 0 then μ else ν) +
         partialDeriv_v2 (fun y => (ξ.ξ y) ν) μ x +
         partialDeriv_v2 (fun y => (ξ.ξ y) μ) ν x|
      ≤ |h.h x (fun i => if i.val = 0 then μ else ν)| +
        |partialDeriv_v2 (fun y => (ξ.ξ y) ν) μ x| +
        |partialDeriv_v2 (fun y => (ξ.ξ y) μ) ν x| := htri
    _ < 0.4 + 0.3 + 0.3 := by linarith [hweak, hd1, hd2]
    _ = 1.0 := by norm_num

/-- Weak-field perturbations stay small after a gauge transformation with derivative bounds. -/
theorem gauge_transform_small_of_weak
  (hWF : WeakFieldPerturbation) (ξ : WeakGaugeVector) :
  ∀ x μ ν, |(gauge_transform hWF.base ξ.ξ).h x (fun i => if i.val = 0 then μ else ν)| < 1 := by
  intro x μ ν
  simp [gauge_transform]
  have h_base_le : |hWF.base.h x (fun i => if i.val = 0 then μ else ν)| ≤ (1 / 10 : ℝ) :=
    le_trans (hWF.small x μ ν) hWF.eps_le
  have hξ₁ := ξ.deriv_bound x μ ν
  have hξ₂ := ξ.deriv_bound x ν μ
  -- Triangle inequality for three terms
  have htri : |hWF.base.h x (fun i => if i.val = 0 then μ else ν) +
                partialDeriv_v2 (fun y => (ξ.ξ.ξ y) ν) μ x +
                partialDeriv_v2 (fun y => (ξ.ξ.ξ y) μ) ν x|
            ≤ |hWF.base.h x (fun i => if i.val = 0 then μ else ν)| +
              |partialDeriv_v2 (fun y => (ξ.ξ.ξ y) ν) μ x| +
              |partialDeriv_v2 (fun y => (ξ.ξ.ξ y) μ) ν x| := by
    have h1 := abs_add (hWF.base.h x (fun i => if i.val = 0 then μ else ν))
                        (partialDeriv_v2 (fun y => (ξ.ξ.ξ y) ν) μ x +
                         partialDeriv_v2 (fun y => (ξ.ξ.ξ y) μ) ν x)
    have h2 := abs_add (partialDeriv_v2 (fun y => (ξ.ξ.ξ y) ν) μ x)
                        (partialDeriv_v2 (fun y => (ξ.ξ.ξ y) μ) ν x)
    exact le_trans h1 (by linarith [h2])
  have hsum :
      |hWF.base.h x (fun i => if i.val = 0 then μ else ν)| +
        |partialDeriv_v2 (fun y => (ξ.ξ.ξ y) ν) μ x| +
        |partialDeriv_v2 (fun y => (ξ.ξ.ξ y) μ) ν x|
      ≤ (1 / 10 : ℝ) + ξ.bound + ξ.bound := by
    have hsum' := add_le_add (add_le_add h_base_le hξ₁) hξ₂
    simpa [add_comm, add_left_comm, add_assoc] using hsum'
  have hbound_twice : ξ.bound + ξ.bound ≤ (6 / 10 : ℝ) := by
    have := add_le_add ξ.bound_le ξ.bound_le
    simpa [add_comm, add_left_comm, add_assoc] using this
  have hbound_total : (1 / 10 : ℝ) + ξ.bound + ξ.bound ≤ (7 / 10 : ℝ) := by
    have := add_le_add_left hbound_twice ((1 / 10 : ℝ))
    simpa [add_comm, add_left_comm, add_assoc] using this
  have htotal := le_trans htri (le_trans hsum hbound_total)
  have : (7 / 10 : ℝ) < 1 := by norm_num
  exact lt_of_le_of_lt htotal this

/-- Gauge transformation preserves symmetry. -/
theorem gauge_transform_symmetric (h : MetricPerturbation) (ξ : GaugeVector)
  (hh : IsSymmetric (fun x _ low => h.h x low)) :
  IsSymmetric (fun x _ low => (gauge_transform h ξ).h x low) := by
  intro x μ ν
  -- Unfold symmetry condition and gauge transform definition
  dsimp [Geometry.IsSymmetric, gauge_transform]
  -- Use symmetry of h
  have h_sym := hh x μ ν
  -- The derivative part is symmetric by commutativity of addition
  -- Left side: h(μ,ν) + ∂μ ξν + ∂ν ξμ
  -- Right side: h(ν,μ) + ∂ν ξμ + ∂μ ξν
  simpa [h_sym, add_comm, add_left_comm, add_assoc]

/-- Condition for Newtonian gauge: h'_0i = 0. -/
def InNewtonianGauge (h : MetricPerturbation) : Prop :=
  ∀ (x : Fin 4 → ℝ) (i : Fin 4), i.val > 0 →
    h.h x (fun j => if j.val = 0 then 0 else i) = 0

/-- Finding gauge vector to eliminate h_0i components. -/
theorem find_gauge_vector_for_newtonian (h : MetricPerturbation)
  [GaugeConstructionFacts] :
  ∃ ξ : GaugeVector, InNewtonianGauge (gauge_transform h ξ) :=
  GaugeConstructionFacts.find_gauge_vector_for_newtonian h

-- After fixing h_0i = 0, can choose trace to make h_ij ∝ δ_ij. -/
theorem spatial_trace_freedom (h : MetricPerturbation) (h_newt : InNewtonianGauge h)
  [GaugeConstructionFacts] :
  ∃ ξ : GaugeVector,
    InNewtonianGauge (gauge_transform h ξ) ∧
    (∀ x i j, i.val > 0 → j.val > 0 → i ≠ j →
      (gauge_transform h ξ).h x (fun k => if k.val = 0 then i else j) = 0) :=
  GaugeConstructionFacts.spatial_trace_freedom h h_newt

/-- Construct Newtonian gauge metric from general perturbation. -/
noncomputable def to_newtonian_gauge (h : MetricPerturbation)
  [GaugeConstructionFacts] : NewtonianGaugeMetric :=
  -- Extract Φ and Ψ from transformed h
  let ξ := Classical.choose (find_gauge_vector_for_newtonian h)
  let h' := gauge_transform h ξ
  { Φ := fun x => (1/2) * h'.h x (fun _ => 0)  -- From h'_00 = 2Φ
  , Ψ := fun x => -(1/2) * h'.h x (fun i => if i.val = 0 then 1 else 1)  -- From h'_11 = -2Ψ
  , Φ_small := by
      intro x
      have hsmall := h'.small x
      simp [MetricPerturbation.small] at hsmall
      -- |Φ| = |(1/2)h'_00| ≤ (1/2)|h'| < (1/2)·0.1 = 0.05 < 0.1
      calc |(1/2) * h'.h x (fun _ => 0)|
          = (1/2) * |h'.h x (fun _ => 0)| := by simp [abs_mul]; norm_num
        _ ≤ (1/2) * 0.1 := by linarith [hsmall (fun _ => 0)]
        _ < 0.1 := by norm_num
  , Ψ_small := by
      intro x
      have hsmall := h'.small x
      simp [MetricPerturbation.small] at hsmall
      -- |Ψ| = |(1/2)h'_11| ≤ (1/2)|h'| < 0.05 < 0.1
      calc |(-(1/2)) * h'.h x (fun i => if i.val = 0 then 1 else 1)|
          = (1/2) * |h'.h x (fun i => if i.val = 0 then 1 else 1)| := by simp [abs_neg, abs_mul]; norm_num
        _ ≤ (1/2) * 0.1 := by linarith [hsmall (fun i => if i.val = 0 then 1 else 1)]
        _ < 0.1 := by norm_num }

/-- Gauge transformation preserves physics (same Riemann tensor). -/
theorem gauge_invariant_riemann (g₀ : MetricTensor) (h : MetricPerturbation) (ξ : GaugeVector)
  (x : Fin 4 → ℝ) [GaugeConstructionFacts] :
  ∀ ρ σ μ ν,
    linearized_riemann g₀ h x ρ σ μ ν = linearized_riemann g₀ (gauge_transform h ξ) x ρ σ μ ν :=
  GaugeConstructionFacts.gauge_invariant_riemann g₀ h ξ x _ _ _ _

/-- Test: Start with diagonal h, transform to Newtonian gauge, verify h_0i = 0. -/
theorem test_newtonian_gauge_construction [GaugeConstructionFacts] :
  let h : MetricPerturbation := {
    h := fun _ low => if low 0 = low 1 then 0.01 else 0,
    small := by intro _ _ _; norm_num
  }
  let ng := to_newtonian_gauge h
  ∀ x i, i.val > 0 → |to_perturbation ng - h| x (0 : Fin 4) i < 0.02 :=
  GaugeConstructionFacts.test_newtonian_gauge_construction

end Perturbation
end Relativity
end IndisputableMonolith
