import IndisputableMonolith.Numerics.Interval.Basic
import IndisputableMonolith.Numerics.Interval.PiBounds
import IndisputableMonolith.Numerics.Interval.Log
import IndisputableMonolith.Numerics.Interval.W8Bounds
import IndisputableMonolith.Constants.Alpha

/-!
# Rigorous Bounds on α⁻¹ (Inverse Fine-Structure Constant)

This module provides interval bounds on alphaInv using the symbolic derivation.
-/

namespace IndisputableMonolith.Numerics

open Interval
open Real (pi log)
open IndisputableMonolith.Constants (alphaInv alpha_seed delta_kappa f_gap w8_from_eight_tick)

/-- alpha_seed = 4π·11 > 138.230048 -/
theorem alpha_seed_gt : (138.230048 : ℝ) < alpha_seed := by
  simp only [alpha_seed]
  have h := four_pi_gt_d6
  linarith

/-- alpha_seed = 4π·11 < 138.230092 -/
theorem alpha_seed_lt : alpha_seed < (138.230092 : ℝ) := by
  simp only [alpha_seed]
  have h := four_pi_lt_d6
  linarith

/-! ## delta_kappa bounds -/

theorem delta_kappa_gt : (-0.003300 : ℝ) < delta_kappa := by
  simp only [delta_kappa]
  have hpi5 := pi_pow5_gt_d6
  have hdenom_gt : 102 * (306.0193 : ℝ) < 102 * pi ^ 5 := by
    have hpi5_pos : 0 < pi ^ 5 := by positivity
    linarith
  have h1 : -(103 : ℝ) / (102 * 306.0193) < -103 / (102 * pi ^ 5) := by
    rw [neg_div, neg_div, neg_lt_neg_iff]
    apply div_lt_div_of_pos_left (by norm_num) (by norm_num) hdenom_gt
  calc (-0.003300 : ℝ) < -103 / (102 * 306.0193) := by norm_num
    _ < -(103 : ℝ) / (102 * pi ^ 5) := h1

theorem delta_kappa_lt : delta_kappa < (-0.003299 : ℝ) := by
  simp only [delta_kappa]
  have hpi5 := pi_pow5_lt_d6
  have hdenom_lt : 102 * pi ^ 5 < 102 * (306.0199 : ℝ) := by
    have hpi5_pos : 0 < pi ^ 5 := by positivity
    linarith
  have h1 : -(103 : ℝ) / (102 * pi ^ 5) < -103 / (102 * 306.0199) := by
    rw [neg_div, neg_div, neg_lt_neg_iff]
    apply div_lt_div_of_pos_left (by norm_num) (by positivity) hdenom_lt
  calc -(103 : ℝ) / (102 * pi ^ 5) < -103 / (102 * 306.0199) := h1
    _ < (-0.003299 : ℝ) := by norm_num

/-! ## f_gap bounds -/

theorem f_gap_gt : (1.195 : ℝ) < f_gap := by
  simp only [f_gap]
  have h_w8_lo := W8Bounds.w8_computed_gt
  have h_log_lo := log_phi_gt_048
  have h_w8_pos : 0 < w8_from_eight_tick := IndisputableMonolith.Constants.w8_pos
  have h_log_lo' : (0.48 : ℝ) < log IndisputableMonolith.Constants.phi := by
    simpa [IndisputableMonolith.Constants.phi, Real.goldenRatio] using h_log_lo
  have h048 : 0 < (0.48 : ℝ) := by norm_num
  -- f_gap = w8 * log(phi) > 2.490564399 * 0.48 = 1.19547...
  calc (1.195 : ℝ) < 2.490564399 * (0.48 : ℝ) := by norm_num
    _ < w8_from_eight_tick * (0.48 : ℝ) := by
      exact mul_lt_mul_of_pos_right h_w8_lo h048
    _ < w8_from_eight_tick * log IndisputableMonolith.Constants.phi := by
      exact mul_lt_mul_of_pos_left h_log_lo' h_w8_pos

theorem f_gap_lt : f_gap < (1.203 : ℝ) := by
  simp only [f_gap]
  have h_w8_hi := W8Bounds.w8_computed_lt
  have h_log_hi := log_phi_lt_0483
  have h_w8_pos : 0 < w8_from_eight_tick := IndisputableMonolith.Constants.w8_pos
  have h_log_hi' : log IndisputableMonolith.Constants.phi < (0.483 : ℝ) := by
    simpa [IndisputableMonolith.Constants.phi, Real.goldenRatio] using h_log_hi
  have h0483 : 0 < (0.483 : ℝ) := by norm_num
  -- f_gap = w8 * log(phi) < 2.490572090 * 0.483 = 1.202946...
  calc w8_from_eight_tick * log IndisputableMonolith.Constants.phi
      < w8_from_eight_tick * (0.483 : ℝ) := by
        exact mul_lt_mul_of_pos_left h_log_hi' h_w8_pos
    _ < (2.490572090 : ℝ) * (0.483 : ℝ) := by
        exact mul_lt_mul_of_pos_right h_w8_hi h0483
    _ < (1.203 : ℝ) := by norm_num

/-! ## alphaInv bounds -/

theorem alphaInv_gt : (137.030 : ℝ) < alphaInv := by
  simp only [alphaInv]
  have h_seed := alpha_seed_gt
  have h_fgap := f_gap_lt
  have h_delta := delta_kappa_lt
  linarith

theorem alphaInv_lt : alphaInv < (137.039 : ℝ) := by
  simp only [alphaInv]
  have h_seed := alpha_seed_lt
  have h_fgap := f_gap_gt
  have h_delta := delta_kappa_gt
  linarith

end IndisputableMonolith.Numerics
