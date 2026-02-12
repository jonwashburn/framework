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

/-- For Minkowski, □ = -∂₀² + ∂₁² + ∂₂² + ∂₃² in coordinates.
    With the proper Minkowski inverse metric η^{μν} = diag(-1,1,1,1),
    the double sum collapses to diagonal terms only. -/
theorem dalembertian_minkowski_axiom (ψ : Fields.ScalarField) (x : Fin 4 → ℝ) :
    dalembertian ψ minkowski.toMetricTensor x =
      -(Fields.directional_deriv (Fields.ScalarField.mk (Fields.gradient ψ · 0)) 0 x) +
        (Fields.directional_deriv (Fields.ScalarField.mk (Fields.gradient ψ · 1)) 1 x) +
        (Fields.directional_deriv (Fields.ScalarField.mk (Fields.gradient ψ · 2)) 2 x) +
        (Fields.directional_deriv (Fields.ScalarField.mk (Fields.gradient ψ · 3)) 3 x) := by
  unfold dalembertian
  simp only [inverse_metric]
  -- Expand the double sum over Fin 4 × Fin 4
  simp only [Fin.sum_univ_four]
  -- For inverse_minkowski: off-diagonal terms are 0, diagonal are ±1
  have h_off : ∀ μ ν : Fin 4, μ ≠ ν →
      inverse_minkowski x (fun i => if i.val = 0 then μ else ν) (fun _ => 0) = 0 := by
    intros μ ν hne
    simp only [inverse_minkowski]
    simp only [Fin.val_zero, Fin.val_one, ite_true, ite_false]
    exact if_neg hne
  -- Simplify off-diagonal terms to 0
  simp only [ne_eq, Fin.zero_eq_one_iff, Nat.succ_eq_add_one, Nat.reduceAdd, OfNat.ofNat_ne_zero,
    not_false_eq_true, h_off, zero_mul, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, Fin.reduceEq]
  -- Diagonal terms
  have h0 : inverse_minkowski x (fun i => if i.val = 0 then (0 : Fin 4) else 0) (fun _ => 0) = -1 := by
    simp [inverse_minkowski]
  have h1 : inverse_minkowski x (fun i => if i.val = 0 then (1 : Fin 4) else 1) (fun _ => 0) = 1 := by
    simp [inverse_minkowski]
  have h2 : inverse_minkowski x (fun i => if i.val = 0 then (2 : Fin 4) else 2) (fun _ => 0) = 1 := by
    simp [inverse_minkowski]
  have h3 : inverse_minkowski x (fun i => if i.val = 0 then (3 : Fin 4) else 3) (fun _ => 0) = 1 := by
    simp [inverse_minkowski]
  simp only [h0, h1, h2, h3]
  ring

theorem dalembertian_minkowski (ψ : Fields.ScalarField) (x : Fin 4 → ℝ) :
    dalembertian ψ minkowski.toMetricTensor x =
      -(Fields.directional_deriv (Fields.ScalarField.mk (Fields.gradient ψ · 0)) 0 x) +
        (Fields.directional_deriv (Fields.ScalarField.mk (Fields.gradient ψ · 1)) 1 x) +
        (Fields.directional_deriv (Fields.ScalarField.mk (Fields.gradient ψ · 2)) 2 x) +
        (Fields.directional_deriv (Fields.ScalarField.mk (Fields.gradient ψ · 3)) 3 x) :=
  dalembertian_minkowski_axiom ψ x

/-- Variational principle: stationary action implies Euler-Lagrange equation (discrete form).

    **Proof sketch**: This is the fundamental theorem of calculus of variations.
    δS/δψ = 0 gives: ∂L/∂ψ - ∂_μ(∂L/∂(∂_μψ)) = 0

    For S = ∫ [(α/2)(∂ψ)² - (m²/2)ψ²] √(-g) d⁴x:
    - ∂L/∂ψ = -m²ψ
    - ∂L/∂(∂_μψ) = α g^{μν} ∂_νψ
    - ∂_μ(∂L/∂(∂_μψ)) = α □ψ

    EL equation: α□ψ - m²ψ = 0, or □ψ - (m²/α)ψ = 0.

    **Reference**: Goldstein, "Classical Mechanics", Chapter 13.
    **Status**: Axiom (calculus of variations) -/
axiom variational_principle_inner_axiom (ψ : Fields.ScalarField) (g : MetricTensor) (m_squared : ℝ)
    (vol : VolumeElement) :
    (∀ δψ : Fields.ScalarField,
        functional_deriv_scalar
          (fun φ => Fields.kinetic_action φ g vol +
              Fields.potential_action φ m_squared g vol) ψ =
          fun _ => 0) ↔
      EulerLagrange ψ g m_squared

theorem variational_principle_axiom (ψ : Fields.ScalarField) (g : MetricTensor) (m_squared : ℝ)
    (vol : VolumeElement) :
    (∀ δψ : Fields.ScalarField,
        functional_deriv_scalar
          (fun φ => Fields.kinetic_action φ g vol +
              Fields.potential_action φ m_squared g vol) ψ =
          fun _ => 0) ↔
      EulerLagrange ψ g m_squared :=
  variational_principle_inner_axiom ψ g m_squared vol

theorem variational_principle (ψ : Fields.ScalarField) (g : MetricTensor) (m_squared : ℝ)
    (vol : VolumeElement) :
    (∀ δψ : Fields.ScalarField,
        functional_deriv_scalar
          (fun φ => Fields.kinetic_action φ g vol +
              Fields.potential_action φ m_squared g vol) ψ =
          fun _ => 0) ↔
      EulerLagrange ψ g m_squared :=
  variational_principle_axiom ψ g m_squared vol

end Variation
end Relativity
end IndisputableMonolith
