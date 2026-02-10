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

/-! ### Canonical constants derived from φ -/

/-- Canonical locked fine-structure constant: α_lock = (1 − 1/φ)/2. -/
@[simp] noncomputable def alphaLock : ℝ := (1 - 1 / phi) / 2

/-- Canonical locked C_lag constant: C_lock = φ^{−5}. -/
@[simp] noncomputable def cLagLock : ℝ := phi ^ (-(5 : ℝ))

lemma alphaLock_pos : 0 < alphaLock := by
  have hφ : 0 < phi := phi_pos
  have hφ_gt : 1 < phi := one_lt_phi
  have hsub : 0 < 1 - 1 / phi := by
    have hlt : 1 / phi < 1 := by
      rw [div_lt_one hφ]
      exact hφ_gt
    exact sub_pos.mpr hlt
  have htwo : 0 < (2 : ℝ) := by norm_num
  unfold alphaLock
  exact div_pos hsub htwo

lemma alphaLock_lt_one : alphaLock < 1 := by
  have hφ : 1 < phi := one_lt_phi
  -- (1 - 1/φ)/2 < 1 ↔ 1 - 1/φ < 2 ↔ -1/φ < 1 ↔ 1/φ > -1 (trivial).
  have hden : 0 < (2 : ℝ) := by norm_num
  have hnum : 1 - 1 / phi < 2 := by
    have hinv_pos : 0 < 1 / phi := div_pos (by norm_num) phi_pos
    have hinv_nonneg : 0 ≤ 1 / phi := le_of_lt hinv_pos
    have h1 : -(1 / phi) ≤ 0 := neg_nonpos.mpr hinv_nonneg
    have h2 : -(1 / phi) < 1 := lt_of_le_of_lt h1 (by norm_num)
    calc
      1 - 1 / phi = 1 + (-(1 / phi)) := by ring
      _ < 1 + 1 := by linarith
      _ = 2 := by norm_num
  have : (1 - 1 / phi) / 2 < (2 : ℝ) / 2 := (div_lt_div_of_pos_right hnum hden)
  unfold alphaLock
  calc
    (1 - 1 / phi) / 2 < (2 : ℝ) / 2 := this
    _ = 1 := by norm_num

lemma cLagLock_pos : 0 < cLagLock := by
  have hphi : 0 < phi := phi_pos
  unfold cLagLock
  exact Real.rpow_pos_of_pos hphi (-(5 : ℝ))

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
