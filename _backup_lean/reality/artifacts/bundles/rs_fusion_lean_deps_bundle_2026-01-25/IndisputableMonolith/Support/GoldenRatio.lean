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

lemma constants_one_add_phi_eq_phi_sq :
    1 + Constants.phi = Constants.phi * Constants.phi := by
  simpa [pow_two, add_comm, mul_comm] using (PhiSupport.phi_squared).symm

@[simp] lemma constants_inv_one_plus_phi_eq_inv_phi_sq :
    (1 + Constants.phi)⁻¹ = Constants.phi⁻¹ * Constants.phi⁻¹ := by
  simp [constants_one_add_phi_eq_phi_sq]

lemma inv_one_plus_phi_eq_inv_phi_sq :
    (1 + Foundation.φ)⁻¹ = Foundation.φ⁻¹ * Foundation.φ⁻¹ := by
  simpa [foundation_phi_eq_constants]
    using constants_inv_one_plus_phi_eq_inv_phi_sq

@[simp] lemma constants_phi_ratio_identity :
  Constants.phi / (1 + Constants.phi) = 1 / Constants.phi := by
  have hφ0 : Constants.phi ≠ 0 := PhiSupport.phi_ne_zero
  simp [div_eq_mul_inv, constants_one_add_phi_eq_phi_sq, hφ0]

lemma phi_ratio_identity : Foundation.φ / (1 + Foundation.φ) = 1 / Foundation.φ := by
  simpa [foundation_phi_eq_constants]
    using constants_phi_ratio_identity

@[simp] lemma constants_inv_phi_add_inv_phi_sq :
    1 / (Constants.phi * Constants.phi) + 1 / Constants.phi = 1 := by
  have hφ0 : Constants.phi ≠ 0 := PhiSupport.phi_ne_zero
  have hden : Constants.phi * Constants.phi ≠ 0 := mul_ne_zero hφ0 hφ0
  calc
    1 / (Constants.phi * Constants.phi) + 1 / Constants.phi
        = 1 / (Constants.phi * Constants.phi) + Constants.phi / (Constants.phi * Constants.phi) := by
            simp [div_eq_mul_inv, hφ0]
    _ = (1 + Constants.phi) / (Constants.phi * Constants.phi) := by
            simpa using (add_div (1 : ℝ) Constants.phi (Constants.phi * Constants.phi)).symm
    _ = 1 := by
            simp [div_eq_mul_inv, constants_one_add_phi_eq_phi_sq, hφ0, hden]

lemma inv_phi_add_inv_phi_sq :
    1 / (Foundation.φ * Foundation.φ) + 1 / Foundation.φ = 1 := by
  simpa [foundation_phi_eq_constants]
    using constants_inv_phi_add_inv_phi_sq

@[simp] lemma inv_phi_add_inv_phi_sq_constants :
    1 / (Constants.phi * Constants.phi) + 1 / Constants.phi = 1 :=
  constants_inv_phi_add_inv_phi_sq

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
  rw [foundation_phi_eq_constants]
  unfold Constants.phi
  exact Real.goldenRatio_irrational

lemma geometric_one_minus_inv_phi_converges :
    0 < (1 - 1 / Foundation.φ) ∧ (1 - 1 / Foundation.φ) < 1 := by
  have h_pos : 0 < 1 / Foundation.φ := inv_phi_pos
  have h_lt_one : 1 / Foundation.φ < 1 := inv_phi_lt_one
  constructor <;> linarith

end GoldenRatio
end Support
end IndisputableMonolith
