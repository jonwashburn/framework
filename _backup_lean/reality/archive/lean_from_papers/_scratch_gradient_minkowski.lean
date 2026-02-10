import IndisputableMonolith.Relativity.Fields.Scalar
import IndisputableMonolith.Relativity.Geometry

namespace IndisputableMonolith.Relativity.Fields

open Geometry

theorem gradient_squared_minkowski_test (φ : ScalarField) (x : Fin 4 → ℝ) :
  gradient_squared φ minkowski_tensor x =
    -(gradient φ x 0)^2 + (gradient φ x 1)^2 + (gradient φ x 2)^2 + (gradient φ x 3)^2 := by
  unfold gradient_squared
  -- Manually expand the sums over Fin 4
  have h_sum_μ : Finset.univ = {0, 1, 2, 3} := rfl
  rw [h_sum_μ]
  repeat (rw [Finset.sum_insert]; swap; simp)
  rw [Finset.sum_singleton]
  -- Now expand ν sum
  have h_sum_ν : Finset.univ = {0, 1, 2, 3} := rfl
  repeat (rw [Finset.sum_insert]; swap; simp)
  rw [Finset.sum_singleton]
  -- Now we have 16 terms. Simplify each inverse_metric evaluation.
  -- First, show inverse_metric minkowski_tensor x is indeed diag(-1, 1, 1, 1)
  have h_inv : ∀ μ ν, inverse_metric minkowski_tensor x (fun i => if i.val = 0 then μ else ν) (fun _ => 0) =
    (if μ = ν then (if μ.val = 0 then -1 else 1) else 0) := by
    intro μ ν
    unfold inverse_metric metric_to_matrix minkowski_tensor eta
    dsimp
    -- This part is the tricky one because of Matrix.inv
    -- For now, let's assume it's correct and see if the rest of the proof works.
    sorry
  simp [h_inv]
  ring

end IndisputableMonolith.Relativity.Fields
