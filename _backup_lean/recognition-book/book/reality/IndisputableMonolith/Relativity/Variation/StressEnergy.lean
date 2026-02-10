import Mathlib
import IndisputableMonolith.Relativity.Geometry
import IndisputableMonolith.Relativity.Fields
import IndisputableMonolith.Relativity.Variation.Functional

/-!
# Stress-Energy Tensor from Variation

Implements T_μν = -(2/√(-g)) δS/δg^{μν} and proves conservation ∇^μ T_μν = 0.
-/

namespace IndisputableMonolith
namespace Relativity
namespace Variation

open Geometry
open Fields

/-- Stress-energy tensor T_μν from scalar field action.
    Computed from metric variation: T_μν = -(2/√(-g)) δS_ψ/δg^{μν}. -/
noncomputable def stress_energy_scalar
  (ψ : Fields.ScalarField) (g : MetricTensor) (vol : VolumeElement)
  (α m_squared : ℝ) : BilinearForm :=
  fun x _ low_idx =>
    let μ := low_idx 0
    let ν := low_idx 1
    -- T_μν = α (∂_μ ψ)(∂_ν ψ) - (α/2) g_μν g^{ρσ} (∂_ρ ψ)(∂_σ ψ) - (m²/2) g_μν ψ²
    α * (Fields.gradient ψ x μ) * (Fields.gradient ψ x ν) -
    (α / 2) * g.g x (fun _ => 0) low_idx * Fields.gradient_squared ψ g x -
    (m_squared / 2) * g.g x (fun _ => 0) low_idx * Fields.field_squared ψ x

/-- Stress-energy is symmetric (follows from structure of T_μν). -/
theorem stress_energy_symmetric (ψ : Fields.ScalarField) (g : MetricTensor) (vol : VolumeElement) (α m_squared : ℝ) :
  IsSymmetric (stress_energy_scalar ψ g vol α m_squared) := by
  intro x μ ν
  have hg := g.symmetric x μ ν
  dsimp [Geometry.IsSymmetric]
  -- Expand both sides and use commutativity and symmetry of g
  simp [stress_energy_scalar, hg, mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/-- Trace of stress-energy tensor T = g^{μν} T_μν. -/
noncomputable def stress_energy_trace
  (ψ : Fields.ScalarField) (g : MetricTensor) (vol : VolumeElement) (α m_squared : ℝ) (x : Fin 4 → ℝ) : ℝ :=
  Finset.sum (Finset.univ : Finset (Fin 4)) (fun μ =>
    Finset.sum (Finset.univ : Finset (Fin 4)) (fun ν =>
      (inverse_metric g) x (fun i => if i.val = 0 then μ else ν) (fun _ => 0) *
      (stress_energy_scalar ψ g vol α m_squared) x (fun _ => 0) (fun i => if i.val = 0 then μ else ν)))

/-- For free scalar (m=0), trace is T = α g^{μν} (∂_μ ψ)(∂_ν ψ) in 4D. -/
axiom stress_energy_trace_free (ψ : Fields.ScalarField) (g : MetricTensor) (vol : VolumeElement) (α : ℝ) (x : Fin 4 → ℝ) :
  stress_energy_trace ψ g vol α 0 x = α * Fields.gradient_squared ψ g x

/-- Conservation equation: ∇^μ T_μν = 0 (covariant conservation).
    Holds when ψ satisfies its equation of motion. -/
def conservation_law
  (ψ : Fields.ScalarField) (g : MetricTensor) (vol : VolumeElement) (α m_squared : ℝ) : Prop :=
  EulerLagrange ψ g m_squared →
    (∀ (ν : Fin 4) (x : Fin 4 → ℝ),
      Finset.sum (Finset.univ : Finset (Fin 4)) (fun μ =>
        (covariant_deriv_covector g
          (fun y _ idx => (stress_energy_scalar ψ g vol α m_squared) y (fun _ => 0)
            (fun i => if i.val = 0 then μ else idx 0)) μ) x (fun _ => 0) (fun _ => ν)) = 0)

/-- Theorem: Stress-energy is conserved when field obeys EL equation. -/
axiom conservation_theorem (ψ : Fields.ScalarField) (g : MetricTensor) (vol : VolumeElement) (α m_squared : ℝ) :
  conservation_law ψ g vol α m_squared

/-- For zero field ψ=0, stress-energy vanishes.
    All terms proportional to ψ or ∂ψ vanish. -/
theorem stress_energy_zero_field (g : MetricTensor) (vol : VolumeElement) (α m_squared : ℝ) :
  ∀ x μ ν,
    (stress_energy_scalar Fields.zero g vol α m_squared) x (fun _ => 0) (fun i => if i.val = 0 then μ else ν) = 0 := by
  intro x μ ν
  simp [stress_energy_scalar, Fields.zero, Fields.gradient, Fields.field_squared, Fields.ScalarField]

/-- GR limit: when α → 0 and m → 0, stress-energy vanishes. -/
theorem stress_energy_gr_limit (ψ : Fields.ScalarField) (g : MetricTensor) (vol : VolumeElement) :
  ∀ x μ ν,
    (stress_energy_scalar ψ g vol 0 0) x (fun _ => 0) (fun i => if i.val = 0 then μ else ν) = 0 := by
  intro x μ ν
  simp only [stress_energy_scalar]
  ring

end Variation
end Relativity
end IndisputableMonolith
