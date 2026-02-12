import Mathlib

namespace IndisputableMonolith
namespace Constants

noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

lemma phi_pos : 0 < phi := by
  have htwo : 0 < (2 : ℝ) := by norm_num
  have hroot_pos : 0 < Real.sqrt 5 := by
    have : (0 : ℝ) < 5 := by norm_num
    simpa using Real.sqrt_pos.mpr this
  have hnum_pos : 0 < 1 + Real.sqrt 5 := by exact add_pos_of_pos_of_nonneg (by norm_num) (le_of_lt hroot_pos)
  simpa [phi] using (div_pos hnum_pos htwo)

lemma one_lt_phi : 1 < phi := by
  have htwo : 0 < (2 : ℝ) := by norm_num
  have hsqrt_gt : Real.sqrt 1 < Real.sqrt 5 := by
    simpa [Real.sqrt_one] using (Real.sqrt_lt_sqrt (by norm_num) (by norm_num : (1 : ℝ) < 5))
  have h2lt : (2 : ℝ) < 1 + Real.sqrt 5 := by
    have h1lt : (1 : ℝ) < Real.sqrt 5 := by simpa [Real.sqrt_one] using hsqrt_gt
    linarith
  have hdiv : (2 : ℝ) / 2 < (1 + Real.sqrt 5) / 2 := (div_lt_div_of_pos_right h2lt htwo)
  have hone_lt : 1 < (1 + Real.sqrt 5) / 2 := by simpa using hdiv
  simpa [phi] using hone_lt

@[simp] noncomputable def alpha_locked : ℝ := (1 - 1 / phi) / 2
@[simp] noncomputable def Clag : ℝ := 1 / (phi ^ (5 : Nat))

lemma alpha_locked_pos : 0 < alpha_locked := by
  have hφ : 1 < phi := one_lt_phi
  have hφpos : 0 < phi := phi_pos
  have hlt : 1 / phi < 1 := by
    have h0 : 0 < (1 : ℝ) := by norm_num
    have : 1 / phi < 1 / 1 := one_div_lt_one_div_of_lt h0 hφ
    simpa [one_div] using this
  have : 0 < 1 - 1 / phi := sub_pos.mpr hlt
  have htwo : 0 < (2 : ℝ) := by norm_num
  exact div_pos this htwo

lemma alpha_locked_lt_one : alpha_locked < 1 := by
  have hlt : (1 - 1 / phi) / 2 < (1 : ℝ) / 2 := by
    have hpos : 0 < 1 / phi := by
      have := inv_pos.mpr phi_pos
      simpa [one_div] using this
    have : 1 - 1 / phi < 1 := by linarith
    have htwo : 0 < (2 : ℝ) := by norm_num
    exact div_lt_div_of_pos_right this htwo
  have : (1 : ℝ) / 2 < 1 := by norm_num
  exact lt_trans hlt this

lemma Clag_pos : 0 < Clag := by
  have hpow : 0 < phi ^ (5 : Nat) := pow_pos phi_pos 5
  simpa [Clag, one_div] using inv_pos.mpr hpow

end Constants
end IndisputableMonolith
