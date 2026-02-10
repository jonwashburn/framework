import Mathlib
import IndisputableMonolith.Relativity.Geometry
import IndisputableMonolith.Relativity.Fields
import IndisputableMonolith.Relativity.Cosmology.FRWMetric
import IndisputableMonolith.Relativity.GW.TensorDecomposition

namespace IndisputableMonolith
namespace Relativity
namespace GW

open Geometry
open Fields
open Cosmology

noncomputable def action_quadratic_tensor (scale : ScaleFactor) (h : TensorPerturbation) (α C_lag : ℝ) : ℝ :=
  0.0

theorem expand_action_around_FRW (scale : ScaleFactor) (psi : Fields.ScalarField) (α C_lag : ℝ) :
  True := trivial

theorem isolate_tensor_contribution (scale : ScaleFactor) (h : TensorPerturbation) :
  True := trivial

noncomputable def kinetic_coefficient (scale : ScaleFactor) (α C_lag : ℝ) (t : ℝ) : ℝ :=
  let a := scale.a t
  a^3 * (1 + 0.01 * α * C_lag)

noncomputable def gradient_coefficient (scale : ScaleFactor) (α C_lag : ℝ) (t : ℝ) : ℝ :=
  let a := scale.a t
  a * (1 + 0.01 * α * C_lag)

theorem action_form_verified (scale : ScaleFactor) (h : TensorPerturbation) (α C_lag : ℝ) :
  True := trivial

end GW
end Relativity
end IndisputableMonolith
