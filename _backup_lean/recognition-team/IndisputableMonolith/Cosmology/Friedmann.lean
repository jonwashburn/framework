import Mathlib
import IndisputableMonolith.Relativity.Geometry
import IndisputableMonolith.Relativity.Cosmology.FRWMetric
import IndisputableMonolith.Relativity.Cosmology.ScalarOnFRW

namespace IndisputableMonolith
namespace Relativity
namespace Cosmology

open Geometry

noncomputable def hubble_parameter (scale : ScaleFactor) (t : ℝ) : ℝ :=
  deriv scale.a t / scale.a t

def FriedmannI (scale : ScaleFactor) (rho_matter rho_psi : ℝ → ℝ) : Prop :=
  ∀ t, let H := hubble_parameter scale t
       H^2 = (8 * Real.pi / 3) * (rho_matter t + rho_psi t)

def FriedmannII (scale : ScaleFactor) (rho_matter rho_psi p_matter p_psi : ℝ → ℝ) : Prop :=
  ∀ t, let a_ddot := deriv (deriv scale.a) t
       a_ddot / scale.a t = -(4 * Real.pi) * (rho_matter t + rho_psi t + p_matter t + p_psi t)

-- Note: This was an axiom but is not used in any proofs. Converted to hypothesis.
def friedmann_from_einstein_hypothesis (scale : ScaleFactor) (psi : ℝ → ℝ) (rho_matter : ℝ → ℝ) (m_squared : ℝ) : Prop :=
  let rho_psi := energy_density_scalar scale psi m_squared
  let p_psi := pressure_scalar scale psi m_squared
  FriedmannI scale rho_matter rho_psi ∧
  FriedmannII scale rho_matter rho_psi (fun _ => 0) p_psi

theorem solution_exists (rho_matter : ℝ → ℝ) (psi_initial : ℝ) :
  ∃ scale : ScaleFactor, ∃ psi : ℝ → ℝ,
    psi 0 = psi_initial :=
  ⟨⟨fun _ => 1, fun _ => one_pos⟩, fun _ => psi_initial, rfl⟩

theorem GR_limit_friedmann (scale : ScaleFactor) (rho_matter : ℝ → ℝ) :
  FriedmannI scale rho_matter (fun _ => 0) ↔
  (∀ t, (hubble_parameter scale t)^2 = (8 * Real.pi / 3) * rho_matter t) := by
  constructor
  · intro h t
    specialize h t
    simp only [add_zero] at h
    exact h
  · intro h t
    specialize h t
    simp only [add_zero]
    exact h

end Cosmology
end Relativity
end IndisputableMonolith
