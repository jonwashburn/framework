import Mathlib
import Mathlib.NumberTheory.Real.GoldenRatio
import IndisputableMonolith.PhiSupport.Lemmas
import IndisputableMonolith.Foundation.RecognitionOperator

/-!
Golden-ratio support lemmas re-exported in the notation used by the ethics layer.
All statements reduce to the Mathlib golden-ratio identities shown in
`IndisputableMonolith.PhiSupport`.
-/

namespace IndisputableMonolith
namespace Support
namespace GoldenRatio

open IndisputableMonolith Foundation Constants

@[simp] lemma foundation_phi_eq_constants : Foundation.φ = Constants.phi := rfl

lemma phi_ne_zero : Foundation.φ ≠ 0 := by
  simpa [foundation_phi_eq_constants] using PhiSupport.phi_ne_zero

lemma one_lt_phi : 1 < Foundation.φ := by
  simpa [foundation_phi_eq_constants] using PhiSupport.one_lt_phi

lemma phi_pos : 0 < Foundation.φ := lt_trans (by norm_num) one_lt_phi

lemma inv_phi_pos : 0 < 1 / Foundation.φ := by
  have h : 0 < Foundation.φ := phi_pos
  simpa using one_div_pos.mpr h

lemma inv_phi_lt_one : 1 / Foundation.φ < 1 := by
  have hpos : 0 < (1 : ℝ) := by norm_num
  have hlt : (1 : ℝ) < Foundation.φ := one_lt_phi
  have := one_div_lt_one_div_of_lt hpos hlt
  simpa using this

lemma phi_squared_eq_phi_plus_one : Foundation.φ * Foundation.φ = Foundation.φ + 1 := by
  have h := PhiSupport.phi_squared
  simpa [foundation_phi_eq_constants, pow_two, add_comm] using h

lemma one_add_phi_eq_phi_sq : 1 + Foundation.φ = Foundation.φ * Foundation.φ := by
  simpa [add_comm, mul_comm] using (phi_squared_eq_phi_plus_one).symm

lemma inv_one_plus_phi_eq_inv_phi_sq :
    1 / (1 + Foundation.φ) = 1 / (Foundation.φ * Foundation.φ) := by
  rw [one_add_phi_eq_phi_sq]

lemma phi_ratio_identity : Foundation.φ / (1 + Foundation.φ) = 1 / Foundation.φ := by
  have hφ0 : Foundation.φ ≠ 0 := phi_ne_zero
  have hden : 1 + Foundation.φ ≠ 0 := by
    have : 0 < 1 + Foundation.φ := by linarith [phi_pos]
    exact ne_of_gt this
  have hsq : Foundation.φ * Foundation.φ = Foundation.φ + 1 := phi_squared_eq_phi_plus_one
  have hleft : Foundation.φ / (1 + Foundation.φ) * Foundation.φ = 1 := by
    have h1 : Foundation.φ / (1 + Foundation.φ) * Foundation.φ =
        Foundation.φ * Foundation.φ / (1 + Foundation.φ) := by
      field_simp [hden]
    rw [h1, hsq, add_comm]
    exact div_self hden
  have hright : 1 / Foundation.φ * Foundation.φ = 1 := by
    field_simp [hφ0]
  have hEq : Foundation.φ / (1 + Foundation.φ) * Foundation.φ =
      1 / Foundation.φ * Foundation.φ := by rw [hleft, hright]
  exact (mul_right_cancel₀ hφ0) hEq

lemma inv_phi_add_inv_phi_sq :
    1 / (Foundation.φ * Foundation.φ) + 1 / Foundation.φ = 1 := by
  have hφ0 : Foundation.φ ≠ 0 := phi_ne_zero
  have hden : 1 + Foundation.φ ≠ 0 := by
    have : 0 < 1 + Foundation.φ := by linarith [phi_pos]
    exact ne_of_gt this
  have hfirst : 1 / (Foundation.φ * Foundation.φ) = 1 / (1 + Foundation.φ) := by
    rw [one_add_phi_eq_phi_sq]
  have hsecond : 1 / Foundation.φ = Foundation.φ / (1 + Foundation.φ) := by
    rw [phi_ratio_identity]
  rw [hfirst, hsecond]
  field_simp [hden]

noncomputable def phi_tier_scale (n : ℤ) : ℝ := Foundation.φ ^ n

lemma phi_tier_scale_pos (n : ℤ) : 0 < phi_tier_scale n := by
  classical
  dsimp [phi_tier_scale]
  cases n with
  | ofNat k =>
      simpa using pow_pos phi_pos k
  | negSucc k =>
      have hpow : 0 < Foundation.φ ^ (Nat.succ k) := pow_pos phi_pos _
      have : 0 < (Foundation.φ ^ (Nat.succ k))⁻¹ := inv_pos.mpr hpow
      simpa [Int.negSucc, zpow_negSucc] using this

lemma phi_irrational : Irrational Foundation.φ := by
  -- Foundation.φ = Constants.phi = Real.goldenRatio (by definition).
  -- Mathlib provides `Real.goldenRatio_irrational : Irrational Real.goldenRatio`.
  have h : Foundation.φ = Real.goldenRatio := by
    simp [foundation_phi_eq_constants, PhiSupport.phi_def]
  rw [h]
  exact Real.goldenRatio_irrational

lemma geometric_one_minus_inv_phi_converges :
    0 < (1 - 1 / Foundation.φ) ∧ (1 - 1 / Foundation.φ) < 1 := by
  have h_pos : 0 < 1 / Foundation.φ := inv_phi_pos
  have h_lt_one : 1 / Foundation.φ < 1 := inv_phi_lt_one
  constructor <;> linarith

end GoldenRatio
end Support
end IndisputableMonolith
