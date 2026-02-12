import Mathlib
import IndisputableMonolith.LightLanguage.Basis.DFT8
import IndisputableMonolith.LightLanguage.Basis.SpectralUniqueness

namespace IndisputableMonolith.LightLanguage.Basis

open Matrix Complex

/-- Eigenvalues of the shift matrix are distinct. -/
lemma shift_eigenvalues_distinct :
    ∀ k1 k2 : Fin 8, k1 ≠ k2 → omega8 ^ k1.val ≠ omega8 ^ k2.val := by
  intro k1 k2 hne h_eq
  have h_ratio : omega8 ^ (k1.val : ℤ - k2.val : ℤ) = 1 := by
    -- omega8 ^ k1 / omega8 ^ k2 = 1
    sorry
  sorry

/-- If B diagonalizes S, its columns are eigenvectors. -/
lemma columns_are_eigenvectors (B : Matrix (Fin 8) (Fin 8) ℂ) (D : Fin 8 → ℂ)
    (hUnit : IsUnitaryMatrix B)
    (hDiag : B.conjTranspose * shift_matrix * B = Matrix.diagonal D) :
    ∀ k, shift_matrix * (fun i => B i k) = D k • (fun i => B i k) := by
  -- B^H * S * B = D  => S * B = B * D
  have h_inv : B * B.conjTranspose = 1 := by
    -- IsUnitaryMatrix means B^H * B = 1. For finite matrices, this implies B * B^H = 1.
    sorry
  have h_comm : shift_matrix * B = B * Matrix.diagonal D := by
    rw [← Matrix.one_mul (shift_matrix * B)]
    rw [← h_inv, Matrix.mul_assoc, Matrix.mul_assoc]
    congr 1
    exact hDiag
  intro k
  funext i
  -- column k of (S*B) is column k of (B*D)
  sorry

end IndisputableMonolith.LightLanguage.Basis
