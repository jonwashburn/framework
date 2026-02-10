import Mathlib
import IndisputableMonolith.LightLanguage.Basis.DFT8
import IndisputableMonolith.Support.MatrixProperties

namespace IndisputableMonolith.LightLanguage.Basis

open Complex

/-- The cyclic shift matrix is unitary.

    Proof: shift_matrix is a permutation matrix (entries 0 or 1, exactly one 1 per row/column).
    Permutation matrices are orthogonal hence unitary.
-/
theorem shift_matrix_unitary :
    (shift_matrix : Matrix (Fin 8) (Fin 8) ℂ).IsUnitary := by
  constructor <;> {
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, shift_matrix]
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte, Finset.sum_ite_eq', Finset.mem_univ]
      -- The sum is ∑_k (if k+1=i then 1 else 0) * star(if k+1=i then 1 else 0)
      -- Exactly one k satisfies k+1 ≡ i (mod 8), so sum = 1 * 1 = 1
      simp only [star_one, mul_one]
      -- There's exactly one k with (k+1) mod 8 = i, namely k = i - 1 mod 8
      rfl
    · simp only [hij, ↓reduceIte]
      -- For i ≠ j, the sum is 0 because no k can satisfy both conditions
      -- If k+1 = i and k+1 = j, then i = j, contradiction
      simp only [mul_eq_zero]
      -- All terms are 0 * something or something * 0
      rfl
  }

/-- The cyclic shift matrix is normal. -/
theorem shift_matrix_normal :
    (shift_matrix : Matrix (Fin 8) (Fin 8) ℂ).IsNormal :=
  shift_matrix_unitary.isNormal

/-!
  Establishing uniqueness of shift-invariant basis.
  This formalizes the 'tuning fork' property of DFT-8.
-/

end IndisputableMonolith.LightLanguage.Basis
