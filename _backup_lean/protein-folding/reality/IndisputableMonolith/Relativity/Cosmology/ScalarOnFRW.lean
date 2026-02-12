import Mathlib
import IndisputableMonolith.Relativity.Geometry
import IndisputableMonolith.Relativity.Calculus
import IndisputableMonolith.Relativity.Fields
import IndisputableMonolith.Relativity.Variation
import IndisputableMonolith.Relativity.Cosmology.FRWMetric

namespace IndisputableMonolith
namespace Relativity
namespace Cosmology

open Geometry
open Calculus
open Fields
open Variation

structure HomogeneousScalar (scale : ScaleFactor) where
  psi : ℝ → ℝ
  -- Homogeneous means ψ = ψ(t) only

noncomputable def klein_gordon_FRW (scale : ScaleFactor) (psi : ℝ → ℝ) (m_squared : ℝ) : ℝ → ℝ :=
  fun t =>
    let H := deriv scale.a t / scale.a t
    deriv (deriv psi) t + 3 * H * deriv psi t + m_squared * psi t

axiom klein_gordon_solution_exists (scale : ScaleFactor) (m_squared : ℝ) :
  ∃ psi : ℝ → ℝ, ∀ t, klein_gordon_FRW scale psi m_squared t = 0

noncomputable def energy_density_scalar (scale : ScaleFactor) (psi : ℝ → ℝ) (m_squared : ℝ) (t : ℝ) : ℝ :=
  (1/2) * (deriv psi t)^2 + (1/2) * m_squared * (psi t)^2

noncomputable def pressure_scalar (scale : ScaleFactor) (psi : ℝ → ℝ) (m_squared : ℝ) (t : ℝ) : ℝ :=
  (1/2) * (deriv psi t)^2 - (1/2) * m_squared * (psi t)^2

theorem energy_pressure_relation (scale : ScaleFactor) (psi : ℝ → ℝ) (m_squared : ℝ) (t : ℝ) :
  energy_density_scalar scale psi m_squared t + pressure_scalar scale psi m_squared t =
    (deriv psi t)^2 := by
  simp [energy_density_scalar, pressure_scalar]
  ring

axiom massless_scalar_not_exactly_radiation (scale : ScaleFactor) (psi : ℝ → ℝ) :
  -- Massless scalar has p = ρ (stiff), not p = ρ/3 (radiation)
  -- This is correct for scalar field
  ∀ t, pressure_scalar scale psi 0 t = energy_density_scalar scale psi 0 t

end Cosmology
end Relativity
end IndisputableMonolith
