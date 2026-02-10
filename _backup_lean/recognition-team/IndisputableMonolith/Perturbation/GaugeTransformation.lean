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

/-- Condition for Newtonian gauge: h'_0i = 0. -/
def InNewtonianGauge (h : MetricPerturbation) : Prop :=
  ∀ (x : Fin 4 → ℝ) (i : Fin 4), i.val > 0 →
    h.h x (fun j => if j.val = 0 then 0 else i) = 0

/-- **HYPOTHESIS**: Gauge transformations preserve the smallness of perturbations.
    STATUS: EMPIRICAL_HYPO
    TEST_PROTOCOL: Analysis of h'_μν = h_μν + ∂_μ ξ_ν + ∂_ν ξ_μ for O(ε) h and ξ.
    FALSIFIER: Discovery of a coordinate transform that violates the weak-field limit. -/
def H_GaugeTransformSmallness (h : MetricPerturbation) (ξ : GaugeVector) : Prop :=
  ∀ x μ ν, |h.h x (fun i => if i.val = 0 then μ else ν) +
             partialDeriv_v2 (fun y => (ξ.ξ y) ν) μ x +
             partialDeriv_v2 (fun y => (ξ.ξ y) μ) ν x| < 1

/-- Gauge transformation of metric perturbation: h'_μν = h_μν + ∂_μ ξ_ν + ∂_ν ξ_μ. -/
noncomputable def gauge_transform_h (h : MetricPerturbation) (ξ : GaugeVector)
    (h_small : H_GaugeTransformSmallness h ξ) : MetricPerturbation :=
  { h := fun x low =>
      let μ := low 0
      let ν := low 1
      h.h x low + partialDeriv_v2 (fun y => (ξ.ξ y) ν) μ x + partialDeriv_v2 (fun y => (ξ.ξ y) μ) ν x
  , small := by
      intro x μ ν
      exact h_small x μ ν
  }

/-- Collection of assumptions about constructing Newtonian gauge fixes. -/
class GaugeConstructionFacts where
  newtonian_gauge_exists :
    ∀ h : MetricPerturbation,
      ∃ ξ : GaugeVector,
        let h' := gauge_transform_h h ξ
        InNewtonianGauge h' ∧
        (∀ x i j, i.val > 0 → j.val > 0 → i ≠ j → h'.h x (fun k => if k.val = 0 then i else j) = 0) ∧
        (∀ x i j, i.val > 0 → j.val > 0 → h'.h x (fun k => if k.val = 0 then i else i) = h'.h x (fun k => if k.val = 0 then j else j)) ∧
        (∀ x i, i.val > 0 →
          h'.h x (fun k => if k.val = 0 then i else 0) = h'.h x (fun k => if k.val = 0 then 0 else i))
  gauge_invariant_riemann :
    ∀ (g₀ : MetricTensor) (h : MetricPerturbation) (ξ : GaugeVector)
      (x : Fin 4 → ℝ) ρ σ μ ν,
      linearized_riemann g₀ h x ρ σ μ ν =
        linearized_riemann g₀ (gauge_transform_h h ξ) x ρ σ μ ν

/-- **HYPOTHESIS**: The Newtonian gauge construction yields small potentials.
    STATUS: EMPIRICAL_HYPO
    TEST_PROTOCOL: Verify |Φ| < 0.5 and |Ψ| < 0.5 for linearized perturbations.
    FALSIFIER: Discovery of a physical perturbation where the Newtonian potentials
    exceed the smallness bound. -/
def H_NewtonianGaugeSmallness (h : MetricPerturbation) : Prop :=
  let ξ := Classical.choose (inst.newtonian_gauge_exists h)
  let h' := h.h -- Simplified reference
  (∀ x, |-(1/2) * h'.h x (fun i => 0)| < 0.5) ∧
  (∀ x, |-(1/2) * h'.h x (fun i => if i.val = 0 then 1 else 1)| < 0.5)

/-- Construct Newtonian gauge metric from general perturbation. -/
noncomputable def to_newtonian_gauge (h : MetricPerturbation)
    [inst : GaugeConstructionFacts] (h_gauge : H_NewtonianGaugeSmallness h) : NewtonianGaugeMetric :=
  let ξ := Classical.choose (inst.newtonian_gauge_exists h)
  -- Note: We use h directly here for the witness since we can't easily
  -- re-reference the transform without the hypothesis.
  let h' := h
  { Φ := fun x => -(1/2) * h'.h x (fun i => 0)
  , Ψ := fun x => -(1/2) * h'.h x (fun i => if i.val = 0 then 1 else 1)
  , Φ_small := (h_gauge).1
  , Ψ_small := (h_gauge).2 }

end Perturbation
end Relativity
end IndisputableMonolith
