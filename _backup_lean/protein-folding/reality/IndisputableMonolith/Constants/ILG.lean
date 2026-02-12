import Mathlib
import IndisputableMonolith.Constants

namespace IndisputableMonolith
namespace Constants

@[simp] noncomputable def alpha_locked : ℝ := (1 - 1 / phi) / 2

@[simp] noncomputable def Clag : ℝ := 1 / (phi ^ (5 : Nat))

lemma alpha_locked_pos : 0 < alpha_locked := by
  dsimp [alpha_locked]
  have hφ : 0 < phi := phi_pos
  have hφ_gt_1 : 1 < phi := one_lt_phi
  have hinv : 0 < 1 / phi := by
    apply div_pos
    · exact zero_lt_one
    · exact hφ
  have hsub : 0 < 1 - 1 / phi := by
    apply sub_pos.mpr
    apply lt_of_lt_of_le hinv
    exact le_refl 1
  have hdiv : 0 < (1 - 1 / phi) / 2 := by
    apply div_pos hsub
    exact zero_lt_two
  exact hdiv

lemma alpha_locked_lt_one : alpha_locked < 1 := by
  dsimp [alpha_locked]
  have hφ : 1 < phi := one_lt_phi
  -- We need to show: (1 - 1/φ) / 2 < 1
  -- Multiply both sides by 2: 1 - 1/φ < 2
  -- Subtract 1: -1/φ < 1
  -- Multiply both sides by -1 (flip inequality): 1/φ > -1
  -- Since φ > 1, this is true, but let me do this more carefully
  calc (1 - 1 / phi) / 2 < 1
    _ ↔ 1 - 1 / phi < 2 := by
      apply div_lt_iff
      exact zero_lt_two
    _ ↔ -1 / phi < 1 := by
      apply sub_lt_sub_right
      exact rfl
    _ ↔ -1 < phi := by
      apply div_lt_right
      · exact lt_of_lt_of_le zero_lt_one (le_of_lt hφ)
      · exact mul_lt_of_lt_left (neg_lt_self zero_lt_one) (inv_pos.mpr hφ)
    _ := lt_trans (neg_lt_self zero_lt_one) hφ

lemma Clag_pos : 0 < Clag := by
  have hφ : 0 < phi := phi_pos
  have hpow : 0 < phi ^ (5 : Nat) := pow_pos hφ 5
  simpa [Clag, one_div] using inv_pos.mpr hpow

end Constants
end IndisputableMonolith
