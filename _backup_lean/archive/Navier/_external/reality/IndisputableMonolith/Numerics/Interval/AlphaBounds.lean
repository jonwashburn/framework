import IndisputableMonolith.Numerics.Interval.Basic
import IndisputableMonolith.Numerics.Interval.PiBounds
import IndisputableMonolith.Numerics.Interval.Log
import IndisputableMonolith.Constants.Alpha

/-!
# Rigorous Bounds on α⁻¹ (Inverse Fine-Structure Constant)

This module provides interval bounds on alphaInv using:
- α⁻¹ = alpha_seed - (f_gap + delta_kappa)
- alpha_seed = 4π·11
- delta_kappa = -103/(102π⁵)
- f_gap = w8 * log(φ) where w8 = 2.488254397846

## Key Results

Using d6 precision bounds on π and [0.48, 0.483] bounds on log(φ):
- alpha_seed ∈ [138.230048, 138.230092]
- delta_kappa ∈ [-0.0032998, -0.0032997]
- f_gap ∈ [1.194, 1.202] (limited by log(φ) precision)
- alphaInv ∈ [137.0315, 137.0390]

This interval contains the target [137.0359, 137.0360].
-/

namespace IndisputableMonolith.Numerics

open Interval
open Real (pi log)
open IndisputableMonolith.Constants (alphaInv alpha_seed delta_kappa f_gap w8_from_eight_tick)

/-- alpha_seed = 4π·11 > 138.230048 -/
theorem alpha_seed_gt : (138.230048 : ℝ) < alpha_seed := by
  simp only [alpha_seed]
  have h := four_pi_gt_d6  -- 12.566368 < 4π
  linarith

/-- alpha_seed = 4π·11 < 138.230092 -/
theorem alpha_seed_lt : alpha_seed < (138.230092 : ℝ) := by
  simp only [alpha_seed]
  have h := four_pi_lt_d6  -- 4π < 12.566372
  linarith

/-- Interval containing alpha_seed -/
def alphaSeedInterval : Interval where
  lo := 138230048 / 1000000  -- 138.230048
  hi := 138230092 / 1000000  -- 138.230092
  valid := by norm_num

/-- alpha_seed is contained in alphaSeedInterval - PROVEN -/
theorem alpha_seed_in_interval : alphaSeedInterval.contains alpha_seed := by
  simp only [contains, alphaSeedInterval]
  constructor
  · have h := alpha_seed_gt
    exact le_of_lt (by calc ((138230048 / 1000000 : ℚ) : ℝ) = (138.230048 : ℝ) := by norm_num
      _ < alpha_seed := h)
  · have h := alpha_seed_lt
    exact le_of_lt (by calc alpha_seed < (138.230092 : ℝ) := h
      _ = ((138230092 / 1000000 : ℚ) : ℝ) := by norm_num)

/-! ## delta_kappa bounds -/

/-- delta_kappa = -103/(102π⁵) is negative -/
theorem delta_kappa_neg : delta_kappa < 0 := by
  simp only [delta_kappa]
  have hpi5_pos : 0 < pi ^ 5 := by positivity
  have hdenom_pos : 0 < 102 * pi ^ 5 := by positivity
  have h : 0 < (103 : ℝ) / (102 * pi ^ 5) := div_pos (by norm_num) hdenom_pos
  have heq : -(103 : ℝ) / (102 * pi ^ 5) = -((103 : ℝ) / (102 * pi ^ 5)) := by ring
  rw [heq]
  linarith

/-- delta_kappa > -0.003300 (using π⁵ > 306.0193)
    Since π⁵ > 306.0193, we have 102·π⁵ > 102·306.0193
    So -103/(102·π⁵) > -103/(102·306.0193) ≈ -0.0033001 > -0.003300 -/
theorem delta_kappa_gt : (-0.003300 : ℝ) < delta_kappa := by
  simp only [delta_kappa]
  have hpi5 := pi_pow5_gt_d6  -- 306.0193 < π⁵
  have hpi5_pos : 0 < pi ^ 5 := by positivity
  have hdenom_pi : 0 < 102 * pi ^ 5 := by positivity
  have hdenom_const : 0 < 102 * (306.0193 : ℝ) := by norm_num
  have hdenom_gt : 102 * (306.0193 : ℝ) < 102 * pi ^ 5 := by linarith
  -- -103/(102·306.0193) < -103/(102·π⁵) since 102·306.0193 < 102·π⁵
  have h1 : -(103 : ℝ) / (102 * 306.0193) < -103 / (102 * pi ^ 5) := by
    rw [neg_div, neg_div, neg_lt_neg_iff]
    apply div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 103) hdenom_const hdenom_gt
  calc (-0.003300 : ℝ) < -103 / (102 * 306.0193) := by norm_num
    _ < -(103 : ℝ) / (102 * pi ^ 5) := h1

/-- delta_kappa < -0.003299 (using π⁵ < 306.0199) -/
theorem delta_kappa_lt : delta_kappa < (-0.003299 : ℝ) := by
  simp only [delta_kappa]
  have hpi5 := pi_pow5_lt_d6  -- π⁵ < 306.0199
  have hpi5_pos : 0 < pi ^ 5 := by positivity
  have hdenom_pi : 0 < 102 * pi ^ 5 := by positivity
  have hdenom_const : 0 < 102 * (306.0199 : ℝ) := by norm_num
  have hdenom_lt : 102 * pi ^ 5 < 102 * (306.0199 : ℝ) := by linarith
  have h1 : -(103 : ℝ) / (102 * pi ^ 5) < -103 / (102 * 306.0199) := by
    rw [neg_div, neg_div, neg_lt_neg_iff]
    apply div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 103) hdenom_pi hdenom_lt
  calc -(103 : ℝ) / (102 * pi ^ 5) < -103 / (102 * 306.0199) := h1
    _ < (-0.003299 : ℝ) := by norm_num

/-! ## f_gap bounds (limited by log(φ) precision)

f_gap = w8 * log(φ) where w8 = 2.488254397846

With log(φ) ∈ [0.48, 0.483]:
f_gap ∈ [2.488254397846 * 0.48, 2.488254397846 * 0.483]
      = [1.19436211096608, 1.201826874159618]
-/

/-- w8 is positive -/
theorem w8_pos : 0 < w8_from_eight_tick := by
  simp only [w8_from_eight_tick]
  norm_num

/-- phi equals goldenRatio -/
theorem phi_eq_goldenRatio : IndisputableMonolith.Constants.phi = Real.goldenRatio := by
  rfl

/-- f_gap > 1.194 (using log(φ) > 0.48 and w8 > 0) -/
theorem f_gap_gt : (1.194 : ℝ) < f_gap := by
  simp only [f_gap]
  have hw8 : w8_from_eight_tick = (2.488254397846 : ℝ) := rfl
  have hlog := log_phi_gt_048  -- 0.48 < log(Real.goldenRatio)
  have hw8_pos := w8_pos
  -- Need to relate Constants.phi to Real.goldenRatio
  have hphi_eq : IndisputableMonolith.Constants.phi = Real.goldenRatio := phi_eq_goldenRatio
  rw [hphi_eq]
  -- f_gap = w8 * log(φ) > w8 * 0.48 = 1.1943...
  have h1 : w8_from_eight_tick * (0.48 : ℝ) < w8_from_eight_tick * log Real.goldenRatio := by
    apply mul_lt_mul_of_pos_left hlog hw8_pos
  have h2 : (1.194 : ℝ) < w8_from_eight_tick * (0.48 : ℝ) := by
    rw [hw8]; norm_num
  linarith

/-- f_gap < 1.202 (using log(φ) < 0.483 and w8 > 0) -/
theorem f_gap_lt : f_gap < (1.202 : ℝ) := by
  simp only [f_gap]
  have hw8 : w8_from_eight_tick = (2.488254397846 : ℝ) := rfl
  have hlog := log_phi_lt_0483  -- log(Real.goldenRatio) < 0.483
  have hw8_pos := w8_pos
  have hphi_eq : IndisputableMonolith.Constants.phi = Real.goldenRatio := phi_eq_goldenRatio
  rw [hphi_eq]
  -- f_gap = w8 * log(φ) < w8 * 0.483 = 1.2018...
  have h1 : w8_from_eight_tick * log Real.goldenRatio < w8_from_eight_tick * (0.483 : ℝ) := by
    apply mul_lt_mul_of_pos_left hlog hw8_pos
  have h2 : w8_from_eight_tick * (0.483 : ℝ) < (1.202 : ℝ) := by
    rw [hw8]; norm_num
  linarith

/-! ## alphaInv bounds

alphaInv = alpha_seed - (f_gap + delta_kappa)

Lower bound: alphaInv > alpha_seed_lo - (f_gap_hi + delta_kappa_hi)
           = 138.230048 - (1.202 + (-0.003299))
           = 138.230048 - 1.198701
           = 137.031347

Upper bound: alphaInv < alpha_seed_hi - (f_gap_lo + delta_kappa_lo)
           = 138.230092 - (1.194 + (-0.003300))
           = 138.230092 - 1.1907
           = 137.039392
-/

/-- alphaInv > 137.031 -/
theorem alphaInv_gt : (137.031 : ℝ) < alphaInv := by
  simp only [alphaInv]
  have h_seed := alpha_seed_gt       -- 138.230048 < alpha_seed
  have h_fgap := f_gap_lt            -- f_gap < 1.202
  have h_delta := delta_kappa_lt     -- delta_kappa < -0.003299
  -- alphaInv = alpha_seed - (f_gap + delta_kappa)
  --          > 138.230048 - (1.202 + (-0.003299))
  --          = 138.230048 - 1.198701
  --          = 137.031347 > 137.031
  linarith

/-- alphaInv < 137.040 -/
theorem alphaInv_lt : alphaInv < (137.040 : ℝ) := by
  simp only [alphaInv]
  have h_seed := alpha_seed_lt       -- alpha_seed < 138.230092
  have h_fgap := f_gap_gt            -- 1.194 < f_gap
  have h_delta := delta_kappa_gt     -- -0.003300 < delta_kappa
  -- alphaInv = alpha_seed - (f_gap + delta_kappa)
  --          < 138.230092 - (1.194 + (-0.003300))
  --          = 138.230092 - 1.1907
  --          = 137.039392 < 137.040
  linarith

/-- Interval containing alphaInv -/
def alphaInvInterval : Interval where
  lo := 137031 / 1000  -- 137.031
  hi := 137040 / 1000  -- 137.040
  valid := by norm_num

/-- The target bounds [137.0359, 137.0360] are contained in our computed interval -/
theorem target_in_alphaInvInterval :
    (137.0359 : ℝ) > alphaInvInterval.lo ∧ (137.0360 : ℝ) < alphaInvInterval.hi := by
  simp only [alphaInvInterval]
  constructor <;> norm_num

end IndisputableMonolith.Numerics
