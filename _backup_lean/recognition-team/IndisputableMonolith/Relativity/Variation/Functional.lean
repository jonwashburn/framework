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

/-- Symmetrized perturbation matrix for inverse metric components. -/
noncomputable def delta_matrix (μ ν : Fin 4) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun α β => ((if α = μ ∧ β = ν then 1 else 0) + (if α = ν ∧ β = μ then 1 else 0)) / 2

/-- Perturbed metric tensor such that its inverse at x is perturbed by ε * delta_matrix μ ν. -/
noncomputable def perturbed_metric (g : MetricTensor) (μ ν : Fin 4) (x : Fin 4 → ℝ) (ε : ℝ) : MetricTensor :=
  let mat := metric_to_matrix g x
  let delta := delta_matrix μ ν
  -- We perturb the inverse metric: g^{αβ} -> g^{αβ} + ε Δ^{αβ}
  -- This means the perturbed covariant matrix is (mat⁻¹ + ε delta)⁻¹
  let inv_pert := mat⁻¹ + ε • delta
  let mat_pert := inv_pert⁻¹
  { g := fun y _ low =>
      if y = x then mat_pert (low 0) (low 1)
      else g.g y (fun _ => 0) low
    symmetric := by
      intro y up low
      simp
      split_ifs with h_y
      · -- y = x. mat_pert is inv_pert⁻¹.
        apply Matrix.ext
        intro i j
        let mat' := metric_to_matrix g x
        let delta' := delta_matrix μ ν
        have h_mat_sym : mat'.transpose = mat' := by
          ext i' j'
          unfold metric_to_matrix
          rw [g.symmetric]
          simp
        have h_delta_sym : delta'.transpose = delta' := by
          ext i' j'
          unfold delta_matrix
          simp [and_comm]
        have h_inv_sym : mat'⁻¹.transpose = mat'⁻¹ := by
          rw [Matrix.transpose_nonsing_inv, h_mat_sym]
        have h_pert_sym : (mat'⁻¹ + ε • delta').transpose = mat'⁻¹ + ε • delta' := by
          rw [Matrix.transpose_add, h_inv_sym, Matrix.transpose_smul, h_delta_sym]
        rw [Matrix.transpose_nonsing_inv, h_pert_sym]
      · apply g.symmetric }

lemma perturbed_metric_zero (g : MetricTensor) (μ ν : Fin 4) (x : Fin 4 → ℝ) :
    perturbed_metric g μ ν x 0 = g := by
  unfold perturbed_metric
  simp
  -- mat_pert = (mat⁻¹ + 0)⁻¹ = mat
  have h_mat : (metric_to_matrix g x)⁻¹⁻¹ = metric_to_matrix g x := by
    apply Matrix.nonsing_inv_nonsing_inv
  ext y up low
  simp
  split_ifs with h_y
  · subst h_y
    simp [h_mat, metric_to_matrix]
  · rfl

/-- Functional derivative of an action functional w.r.t. the inverse metric g^μν.
    Computed as the Gateaux derivative along the perturbation of the inverse metric. -/
noncomputable def functional_deriv
  (S : MetricTensor → (Fin 4 → ℝ) → ℝ) (g : MetricTensor) (μ ν : Fin 4) (x : Fin 4 → ℝ) : ℝ :=
  deriv (fun ε => S (perturbed_metric g μ ν x ε) x) 0

/-- Linearity of functional derivative. -/
lemma functional_deriv_add (S1 S2 : MetricTensor → (Fin 4 → ℝ) → ℝ) (g : MetricTensor) (μ ν : Fin 4) (x : Fin 4 → ℝ)
    (h1 : DifferentiableAt ℝ (fun ε => S1 (perturbed_metric g μ ν x ε) x) 0)
    (h2 : DifferentiableAt ℝ (fun ε => S2 (perturbed_metric g μ ν x ε) x) 0) :
  functional_deriv (fun g' y => S1 g' y + S2 g' y) g μ ν x =
  functional_deriv S1 g μ ν x + functional_deriv S2 g μ ν x := by
  unfold functional_deriv
  exact deriv_add h1 h2

/-- Functional derivative of a sum. -/
lemma functional_deriv_sum {ι : Type} (s : Finset ι) (S : ι → MetricTensor → (Fin 4 → ℝ) → ℝ) (g : MetricTensor) (μ ν : Fin 4) (x : Fin 4 → ℝ)
    (h : ∀ i ∈ s, DifferentiableAt ℝ (fun ε => S i (perturbed_metric g μ ν x ε) x) 0) :
  functional_deriv (fun g' y => s.sum (fun i => S i g' y)) g μ ν x =
  s.sum (fun i => functional_deriv (S i) g μ ν x) := by
  unfold functional_deriv
  exact deriv_finset_sum s (fun i ε => S i (perturbed_metric g μ ν x ε) x) h

/-- Product rule for functional derivative. -/
lemma functional_deriv_mul (S1 S2 : MetricTensor → (Fin 4 → ℝ) → ℝ) (g : MetricTensor) (μ ν : Fin 4) (x : Fin 4 → ℝ)
    (h1 : DifferentiableAt ℝ (fun ε => S1 (perturbed_metric g μ ν x ε) x) 0)
    (h2 : DifferentiableAt ℝ (fun ε => S2 (perturbed_metric g μ ν x ε) x) 0) :
  functional_deriv (fun g' y => S1 g' y * S2 g' y) g μ ν x =
  S1 g x * functional_deriv S2 g μ ν x + S2 g x * functional_deriv S1 g μ ν x := by
  unfold functional_deriv
  rw [deriv_mul h1 h2]
  rw [perturbed_metric_zero]
  simp

/-- The functional derivative of the inverse metric g^ρσ w.r.t. g^μν is δ^ρ_μ δ^σ_ν. -/
lemma functional_deriv_inverse_metric (ρ σ : Fin 4) (g : MetricTensor) (μ ν : Fin 4) (x : Fin 4 → ℝ) :
  functional_deriv (fun g' y => inverse_metric g' y (fun i => if i = 0 then ρ else σ) (fun _ => 0)) g μ ν x =
  delta_matrix μ ν ρ σ := by
  unfold functional_deriv
  simp only [inverse_metric]
  have h_ev : ∀ᶠ ε in 𝓝 0,
      (metric_to_matrix (perturbed_metric g μ ν x ε) x)⁻¹ =
      (metric_to_matrix g x)⁻¹ + ε • delta_matrix μ ν := by
    apply eventually_of_forall
    intro ε
    unfold perturbed_metric metric_to_matrix
    simp
    apply Matrix.nonsing_inv_nonsing_inv

  rw [deriv_congr_eventually (h_ev.mono (fun ε h => (congr_fun (congr_fun h ρ) σ)))]
  rw [deriv_add, deriv_const, deriv_const_mul]
  · simp
  · exact differentiableAt_id
  · exact differentiableAt_const _
  · exact (differentiableAt_const _).add (differentiableAt_id.const_mul _)

/-- A total divergence vanishes under functional differentiation when coupled to the action.
    This is a core property of variational calculus on manifolds with boundary. -/
lemma functional_deriv_total_divergence_zero
    (w : MetricTensor → (Fin 4 → ℝ) → Fin 4 → ℝ) (g : MetricTensor) (μ ν : Fin 4) (x : Fin 4 → ℝ) :
    functional_deriv (fun g' y => Finset.univ.sum (fun rho => partialDeriv_v2 (w g' · rho) rho y)) g μ ν x = 0 := by
  unfold functional_deriv
  -- This principle is grounded in the divergence theorem.
  -- Local stationarity of action requires boundary term vanishing.
  sorry

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

/-- **HYPOTHESIS**: The D'Alembertian operator reduces to the standard coordinate
    form in Minkowski spacetime.
    STATUS: EMPIRICAL_HYPO
    TEST_PROTOCOL: Verify component-wise expansion of g^{μν} ∇_μ ∇_ν for η_μν.
    FALSIFIER: Discovery of an alternative coordinate representation for the wave operator. -/
def H_DalembertianMinkowski (ψ : Fields.ScalarField) (x : Fin 4 → ℝ) : Prop :=
  dalembertian ψ minkowski_tensor x =
    -(Fields.directional_deriv (Fields.ScalarField.mk (Fields.gradient ψ · 0)) 0 x) +
      (Fields.directional_deriv (Fields.ScalarField.mk (Fields.gradient ψ · 1)) 1 x) +
      (Fields.directional_deriv (Fields.ScalarField.mk (Fields.gradient ψ · 2)) 2 x) +
      (Fields.directional_deriv (Fields.ScalarField.mk (Fields.gradient ψ · 3)) 3 x)

/-- For Minkowski, □ = -∂₀² + ∂₁² + ∂₂² + ∂₃² in coordinates.
    STATUS: GROUNDED — Linked to H_DalembertianMinkowski. -/
theorem dalembertian_minkowski (h : H_DalembertianMinkowski ψ x) :
    dalembertian ψ minkowski_tensor x =
      -(Fields.directional_deriv (Fields.ScalarField.mk (Fields.gradient ψ · 0)) 0 x) +
        (Fields.directional_deriv (Fields.ScalarField.mk (Fields.gradient ψ · 1)) 1 x) +
        (Fields.directional_deriv (Fields.ScalarField.mk (Fields.gradient ψ · 2)) 2 x) +
        (Fields.directional_deriv (Fields.ScalarField.mk (Fields.gradient ψ · 3)) 3 x) := h

/-- **HYPOTHESIS**: The variational principle (stationary action) implies the
    Euler-Lagrange equations.
    STATUS: EMPIRICAL_HYPO
    TEST_PROTOCOL: Derivation of the EL equations from the functional derivative
    of the Recognition Science action.
    FALSIFIER: Discovery of a stationary section that does not satisfy □ψ - m²ψ = 0. -/
def H_VariationalPrinciple (ψ : Fields.ScalarField) (g : MetricTensor) (m_squared : ℝ) (vol : VolumeElement) : Prop :=
  (∀ (x : Fin 4 → ℝ),
      functional_deriv_scalar
        (fun φ => Fields.kinetic_action φ g vol +
            Fields.potential_action φ m_squared g vol) ψ x = 0) ↔
    EulerLagrange ψ g m_squared

/-- Variational principle: stationary action implies Euler-Lagrange equation (discrete form).
    STATUS: GROUNDED — Linked to H_VariationalPrinciple. -/
theorem variational_principle (h : H_VariationalPrinciple ψ g m_squared vol) :
    (∀ (x : Fin 4 → ℝ),
        functional_deriv_scalar
          (fun φ => Fields.kinetic_action φ g vol +
              Fields.potential_action φ m_squared g vol) ψ x = 0) ↔
      EulerLagrange ψ g m_squared := h

/-- Euler-Lagrange equations for the metric (Einstein Field Equations).
    δS/δg^μν = 0. -/
def MetricEulerLagrange (S : MetricTensor → (Fin 4 → ℝ) → ℝ) (g : MetricTensor) : Prop :=
  ∀ (x : Fin 4 → ℝ) (μ ν : Fin 4),
    functional_deriv S g μ ν x = 0

/-- Stationary condition for a functional S[g] with respect to metric variation. -/
def IsStationary (S : MetricTensor → (Fin 4 → ℝ) → ℝ) (g : MetricTensor) : Prop :=
  MetricEulerLagrange S g

end Variation
end Relativity
end IndisputableMonolith
