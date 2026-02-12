import Mathlib

namespace IndisputableMonolith
namespace Constants

/-- Golden ratio φ as a concrete real. -/
noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

lemma phi_pos : 0 < phi := by
  have htwo : 0 < (2 : ℝ) := by norm_num
  -- Use that √5 > 0
  have hroot_pos : 0 < Real.sqrt 5 := by
    have : (0 : ℝ) < 5 := by norm_num
    exact Real.sqrt_pos.mpr this
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

lemma phi_ge_one : 1 ≤ phi := le_of_lt one_lt_phi
lemma phi_ne_zero : phi ≠ 0 := ne_of_gt phi_pos
lemma phi_ne_one : phi ≠ 1 := ne_of_gt one_lt_phi

/-- Minimal RS units used in Core. -/
structure RSUnits where
  tau0 : ℝ
  ell0 : ℝ
  c    : ℝ
  c_ell0_tau0 : c * tau0 = ell0

/-- Minimal global constant K placeholder. -/
@[simp] def K : ℝ := 1

lemma K_pos : 0 < K := by simp [K]
lemma K_nonneg : 0 ≤ K := by simp [K]

end Constants
end IndisputableMonolith
