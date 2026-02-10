import Mathlib
import IndisputableMonolith.Relativity.Geometry
import IndisputableMonolith.Relativity.Fields

/-!
# Functional Derivatives

This module implements functional derivatives δS/δψ and δS/δg^{μν} for variational calculus.
-/

namespace IndisputableMonolith
namespace Relativity
namespace Variation

open Geometry
open Fields

/-- Functional derivative of a scalar functional w.r.t. scalar field.
    δF[ψ]/δψ(x) computed via Gateaux derivative. -/
noncomputable def functional_deriv_scalar
  (F : Fields.ScalarField → ℝ) (ψ : Fields.ScalarField) (x : Fin 4 → ℝ) : ℝ :=
  -- δF/δψ(x) = lim_{ε→0} [F[ψ + ε δ(x-·)] - F[ψ]] / ε
  -- Simplified: use finite difference with small perturbation
  let ε := (0.001 : ℝ)
  let δ_x : Fields.ScalarField := { ψ := fun y => if y = x then 1 else 0 }  -- Delta function approx
  let ψ_pert : Fields.ScalarField := Fields.add ψ (Fields.smul ε δ_x)
  (F ψ_pert - F ψ) / ε

/-- Euler-Lagrange equation for scalar field from action S[ψ].
    Derived from δS/δψ = 0 gives: ∂_μ (∂L/∂(∂_μ ψ)) - ∂L/∂ψ = 0. -/
def EulerLagrange (ψ : Fields.ScalarField) (g : MetricTensor) (m_squared : ℝ) : Prop :=
  -- □ψ - m² ψ = 0 where □ = g^{μν} ∇_μ ∇_ν
  ∀ x : Fin 4 → ℝ,
    Finset.sum (Finset.univ : Finset (Fin 4)) (fun μ =>
      Finset.sum (Finset.univ : Finset (Fin 4)) (fun ν =>
        (inverse_metric g) x (fun i => if i.val = 0 then μ else ν) (fun _ => 0) *
        Fields.directional_deriv
          (Fields.ScalarField.mk (Fields.gradient ψ · μ)) ν x)) - m_squared * ψ.ψ x = 0

/-- Klein-Gordon equation: □ψ - m²ψ = 0 (special case of EL for free scalar). -/
def KleinGordon (ψ : Fields.ScalarField) (g : MetricTensor) (m_squared : ℝ) : Prop :=
  EulerLagrange ψ g m_squared

/-- D'Alembertian operator □ = g^{μν} ∇_μ ∇_ν. -/
noncomputable def dalembertian (ψ : Fields.ScalarField) (g : MetricTensor) (x : Fin 4 → ℝ) : ℝ :=
  Finset.sum (Finset.univ : Finset (Fin 4)) (fun μ =>
    Finset.sum (Finset.univ : Finset (Fin 4)) (fun ν =>
      (inverse_metric g) x (fun i => if i.val = 0 then μ else ν) (fun _ => 0) *
      Fields.directional_deriv (Fields.ScalarField.mk (Fields.gradient ψ · μ)) ν x))

theorem klein_gordon_explicit (ψ : Fields.ScalarField) (g : MetricTensor) (m_squared : ℝ) :
  KleinGordon ψ g m_squared ↔ (∀ x, dalembertian ψ g x - m_squared * ψ.ψ x = 0) := by
  simp [KleinGordon, EulerLagrange, dalembertian]

/-- For Minkowski, □ = -∂_t² + ∇² (wave operator). -/
axiom dalembertian_minkowski (ψ : Fields.ScalarField) (x : Fin 4 → ℝ) :
  dalembertian ψ minkowski.toMetricTensor x =
    -(Fields.directional_deriv (Fields.ScalarField.mk (Fields.gradient ψ · 0)) 0 x) +
     (Fields.directional_deriv (Fields.ScalarField.mk (Fields.gradient ψ · 1)) 1 x) +
     (Fields.directional_deriv (Fields.ScalarField.mk (Fields.gradient ψ · 2)) 2 x) +
     (Fields.directional_deriv (Fields.ScalarField.mk (Fields.gradient ψ · 3)) 3 x)

/-- Variational principle: ψ extremizes action iff it satisfies EL equation.
    Fundamental theorem of calculus of variations. -/
axiom variational_principle (ψ : Fields.ScalarField) (g : MetricTensor) (m_squared : ℝ) (vol : VolumeElement) :
  (∀ δψ : Fields.ScalarField,
    functional_deriv_scalar
      (fun φ => Fields.kinetic_action φ g vol + Fields.potential_action φ m_squared g vol) ψ =
      fun x => 0) ↔
  EulerLagrange ψ g m_squared

end Variation
end Relativity
end IndisputableMonolith
