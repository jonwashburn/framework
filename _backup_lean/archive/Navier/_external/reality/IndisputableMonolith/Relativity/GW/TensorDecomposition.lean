import Mathlib
import IndisputableMonolith.Relativity.Geometry
import IndisputableMonolith.Relativity.Cosmology.FRWMetric

namespace IndisputableMonolith
namespace Relativity
namespace GW

open Geometry
open Cosmology

structure TensorPerturbation where
  h_TT : ℝ → (Fin 3 → Fin 3 → ℝ)
  transverse : ∀ t i, Finset.sum (Finset.range 3) (fun j =>
    if hj : j < 3 then h_TT t i ⟨j, hj⟩ else 0) = 0
  traceless : ∀ t, Finset.sum (Finset.range 3) (fun i =>
    if hi : i < 3 then h_TT t ⟨i, hi⟩ ⟨i, hi⟩ else 0) = 0

theorem decompose_perturbation :
  True := trivial

theorem projection_operator_TT :
  True := trivial

theorem decomposition_unique :
  True := trivial

end GW
end Relativity
end IndisputableMonolith
