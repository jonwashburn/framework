import IndisputableMonolith.LightLanguage.Basis.SpectralUniqueness
import IndisputableMonolith.Support.MatrixProperties

namespace IndisputableMonolith.LightLanguage

open Basis
open Complex

/-- The cyclic shift operator S on 8-vectors. -/
noncomputable def S : Matrix (Fin 8) (Fin 8) ℂ := shift_matrix

/-- **Phase 2 Derivation**: DFT modes are eigenvectors of the shift operator. -/
theorem dft8_modes_are_eigenvectors (k : Fin 8) :
    cyclic_shift (dft8_mode k) = (omega8 ^ k.val) • (dft8_mode k) :=
  dft8_shift_eigenvector k

/-- The DFT matrix diagonalizes the shift matrix. -/
theorem dft8_diagonalizes_S :
    dft8_matrix.conjTranspose * S * dft8_matrix =
    Matrix.diagonal (fun k => omega8 ^ k.val) :=
  dft8_diagonalizes_shift

/-- Eigenvalues of the 8-tick shift operator are the 8th roots of unity. -/
theorem shift_eigenvalues_are_roots :
    ∀ k : Fin 8, (omega8 ^ k.val) ^ 8 = 1 := by
  intro k
  rw [← pow_mul, mul_comm, pow_mul, omega8_pow_8, one_pow]

/-- The eigenvalues of the shift operator are distinct. -/
theorem shift_eigenvalues_distinct :
    Function.Injective (fun k : Fin 8 => omega8 ^ k.val) := by
  intro k1 k2 h
  have h1 : k1.val < 8 := k1.isLt
  have h2 : k2.val < 8 := k2.isLt
  rcases lt_trichotomy k1.val k2.val with hlt | heq | hgt
  · have hd_pos : 0 < k2.val - k1.val := Nat.sub_pos_of_lt hlt
    have hd_lt : k2.val - k1.val < 8 := Nat.lt_of_le_of_lt (Nat.sub_le k2.val k1.val) h2
    have h_one : omega8 ^ (k2.val - k1.val) = 1 := by
      have h_mul : omega8 ^ k1.val * omega8 ^ (k2.val - k1.val) = omega8 ^ k2.val := by
        rw [← pow_add, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt hlt)]
      have h_phi : omega8 ^ k1.val = omega8 ^ k2.val := h
      rw [h_phi] at h_mul
      have hne0 : omega8 ^ k2.val ≠ 0 := by
        apply pow_ne_zero
        simp only [omega8]
        exact exp_ne_zero _
      exact mul_left_cancel₀ hne0 (h_mul.trans (mul_one (omega8 ^ k2.val)).symm)
    exact (omega8_pow_ne_one _ hd_pos hd_lt h_one).elim
  · exact Fin.ext heq
  · have hd_pos : 0 < k1.val - k2.val := Nat.sub_pos_of_lt hgt
    have hd_lt : k1.val - k2.val < 8 := Nat.lt_of_le_of_lt (Nat.sub_le k1.val k2.val) h1
    have h_one : omega8 ^ (k1.val - k2.val) = 1 := by
      have h_mul : omega8 ^ k2.val * omega8 ^ (k1.val - k2.val) = omega8 ^ k1.val := by
        rw [← pow_add, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt hgt)]
      have h_phi : omega8 ^ k1.val = omega8 ^ k2.val := h
      rw [← h_phi] at h_mul
      have hne0 : omega8 ^ k1.val ≠ 0 := by
        apply pow_ne_zero
        simp only [omega8]
        exact exp_ne_zero _
      exact mul_left_cancel₀ hne0 (h_mul.trans (mul_one (omega8 ^ k1.val)).symm)
    exact (omega8_pow_ne_one _ hd_pos hd_lt h_one).elim

/-- **Phase 2 Derivation**: DFT modes are the unique eigenmodes of the shift operator.
    Establishing uniqueness of shift-invariant basis (Retires Axiom A2). -/
theorem dft8_is_natural_tuning_fork :
    ∀ (B : Matrix (Fin 8) (Fin 8) ℂ),
      B.IsUnitary →
      (∃ D : Fin 8 → ℂ, B.conjTranspose * S * B = Matrix.diagonal D) →
      (∃ (phases : Fin 8 → ℂ) (perm : Equiv.Perm (Fin 8)),
        (∀ k, ‖phases k‖ = 1) ∧
        ∀ t k, B t k = phases k * dft8_matrix t (perm k)) := by
  intro B hUnit hDiag
  exact Basis.spectral_uniqueness_dft8 B hUnit hDiag

end IndisputableMonolith.LightLanguage
