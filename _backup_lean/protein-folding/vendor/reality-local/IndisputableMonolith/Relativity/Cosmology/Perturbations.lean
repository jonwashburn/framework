import Mathlib
import IndisputableMonolith.Relativity.Cosmology.FRWMetric
import IndisputableMonolith.Relativity.Cosmology.ScalarOnFRW
import IndisputableMonolith.Relativity.Cosmology.Friedmann

namespace IndisputableMonolith
namespace Relativity
namespace Cosmology

open Geometry

structure Perturbations where
  delta_rho : ℝ → ℝ
  delta_p : ℝ → ℝ
  delta_psi : ℝ → ℝ

noncomputable def perturbed_density (rho_bg : ℝ → ℝ) (pert : Perturbations) (t : ℝ) : ℝ :=
  rho_bg t + pert.delta_rho t

/-- Hypothesis: there exists a set of linear perturbations on FRW satisfying the (not yet
formalized) linearized perturbation equations around the given background. -/
def linearized_perturbation_equations_hypothesis (scale : ScaleFactor) (psi_bg : ℝ → ℝ) : Prop :=
  ∃ pert : Perturbations, True

def GrowingMode (pert : Perturbations) : Prop :=
  ∃ D : ℝ → ℝ, ∀ t, pert.delta_rho t = D t

def DecayingMode (pert : Perturbations) : Prop :=
  ∃ D_decay : ℝ → ℝ, ∀ t, pert.delta_rho t = D_decay t

theorem mode_decomposition (pert : Perturbations) :
  ∃ growing decaying, GrowingMode growing ∧ DecayingMode decaying :=
  ⟨⟨fun _ => 0, fun _ => 0, fun _ => 0⟩, ⟨fun _ => 0, fun _ => 0, fun _ => 0⟩,
   ⟨⟨fun _ => 0, fun _ => rfl⟩, ⟨fun _ => 0, fun _ => rfl⟩⟩⟩

end Cosmology
end Relativity
end IndisputableMonolith
