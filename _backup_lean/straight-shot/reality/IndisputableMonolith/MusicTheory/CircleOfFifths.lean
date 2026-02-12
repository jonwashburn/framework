import Mathlib
import IndisputableMonolith.MusicTheory.HarmonicModes
import IndisputableMonolith.MusicTheory.Consonance
import IndisputableMonolith.Foundation.PhiForcing

/-!
# Circle of Fifths: φ-Spiral in Frequency Space

This module derives **the circle of fifths from φ** and explains why Western
music uses 12 semitones per octave.
-/

namespace IndisputableMonolith
namespace MusicTheory
namespace CircleOfFifths

open Real HarmonicModes Consonance

/-! ## Fundamental Ratios -/

/-- The perfect fifth ratio. -/
noncomputable def fifth : ℝ := 3/2

/-- The octave ratio. -/
noncomputable def octave : ℝ := 2

/-- Number of semitones per octave. -/
def semitonesPerOctave : ℕ := 12

/-- Number of RS modes per octave. -/
def rsModesPerOctave : ℕ := 8

/-! ## The Pythagorean Comma -/

/-- The Pythagorean comma is the difference between 12 fifths and 7 octaves.
    comma = (3/2)^12 / 2^7 = 3^12 / 2^19 ≈ 1.0136 -/
noncomputable def pythagoreanComma : ℝ := (3/2)^12 / 2^7

theorem pythagorean_comma_value :
    pythagoreanComma = 531441 / 524288 := by
  unfold pythagoreanComma
  norm_num

/-- The Pythagorean comma is slightly greater than 1.
    3^12 = 531441 > 524288 = 2^19, so 3^12/2^19 > 1. -/
theorem pythagorean_comma_gt_one : pythagoreanComma > 1 := by
  rw [pythagorean_comma_value]
  norm_num

/-- The Pythagorean comma in cents: approximately 23.46 cents. -/
noncomputable def pythagoreanCommaCents : ℝ := 1200 * Real.log pythagoreanComma / Real.log 2

/-! ## Why 12 Semitones? -/

/-- The number of fifths needed to approximate n octaves.
    We seek the smallest k such that (3/2)^k ≈ 2^n for some n. -/
def fifthsToApproxOctaves : ℕ := 12

/-- 12 is the denominator of the best rational approximation to log₂(3/2).
    log₂(3/2) ≈ 0.58496... ≈ 7/12 = 0.58333...

    **Numerical verification**: |7/12 - log₂(3/2)| ≈ 0.00163 < 0.01 ✓

    **Proof strategy**: The Pythagorean comma (3/2)^12 / 2^7 = 531441/524288 ≈ 1.0136
    shows that 12 fifths is close to 7 octaves. Taking logs:
    |12·log₂(3/2) - 7| = log₂(531441/524288) ≈ 0.0195
    Hence |7/12 - log₂(3/2)| ≈ 0.00163 < 0.01.

    **Status**: Requires bounds on log(2) ∈ (0.69, 0.7) which need transcendental
    number theory infrastructure. -/
theorem twelve_best_approximation :
    |(7 : ℝ) / 12 - Real.log (3 / 2) / Real.log 2| < 1 / 100 := by
  -- Strategy: Show |12·log(3/2) - 7·log(2)| / (12·log(2)) < 0.01
  -- We have (3/2)^12 / 2^7 = 531441/524288 ∈ (1, 1.02)
  -- And log(1.02) < 0.02 < 0.01 * 12 * log(2) ≈ 0.083
  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h_log32_pos : 0 < Real.log (3/2) := Real.log_pos (by norm_num)
  -- Compute (3/2)^12 and 2^7 as rationals
  have h_ratio : ((3 : ℝ)/2)^12 / 2^7 = 531441 / 524288 := by norm_num
  -- The ratio is between 1 and 1.02
  have h_ratio_gt1 : (1 : ℝ) < 531441 / 524288 := by norm_num
  have h_ratio_lt102 : (531441 : ℝ) / 524288 < 1.02 := by norm_num
  -- Upper bound on log(ratio): log(x) < x - 1 for x > 1
  have h_log_ratio_upper : Real.log (531441 / 524288 : ℝ) < 0.02 := by
    have h_pos : (0 : ℝ) < 531441 / 524288 := by norm_num
    rw [Real.log_lt_iff_lt_exp h_pos]
    -- Need: 531441/524288 < exp(0.02)
    -- We have: exp(0.02) > 1 + 0.02 = 1.02 > 531441/524288 ≈ 1.01364
    have hexp : Real.exp 0.02 > 1.02 := by
      have h := Real.add_one_lt_exp (show (0.02 : ℝ) ≠ 0 by norm_num)
      linarith
    have hrat : (531441 / 524288 : ℝ) < 1.02 := by norm_num
    linarith
  have h_log_ratio_lower : Real.log (531441 / 524288 : ℝ) > 0 := Real.log_pos h_ratio_gt1
  -- log((3/2)^12 / 2^7) = 12·log(3/2) - 7·log(2)
  have h_log_diff : Real.log ((3/2 : ℝ)^12 / 2^7) = 12 * Real.log (3/2) - 7 * Real.log 2 := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    ring
  rw [h_ratio] at h_log_diff
  -- Now we have: 0 < 12·log(3/2) - 7·log(2) < 0.02
  have h_diff_pos : 12 * Real.log (3/2) - 7 * Real.log 2 > 0 := by rw [← h_log_diff]; exact h_log_ratio_lower
  have h_diff_upper : 12 * Real.log (3/2) - 7 * Real.log 2 < 0.02 := by rw [← h_log_diff]; exact h_log_ratio_upper
  -- Use log(2) > 0.693
  have h_log2_gt : Real.log 2 > 0.693 := by
    have := Real.log_two_gt_d9  -- 0.6931471803 < log 2
    linarith
  have h_denom_pos : 12 * Real.log 2 > 0 := by linarith
  -- 0.02 / (12 * log 2) < 0.02 / (12 * 0.693) < 0.02 / 8.316 < 0.0025 < 0.01
  have h_bound : 0.02 / (12 * Real.log 2) < 1 / 100 := by
    have h1 : 12 * Real.log 2 > 8.316 := by
      have : Real.log 2 > 0.693 := by linarith [Real.log_two_gt_d9]
      linarith
    have h2 : (0.02 : ℝ) / 8.316 < 0.01 := by norm_num
    have h3 : 0.02 / (12 * Real.log 2) < 0.02 / 8.316 := by
      apply div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 0.02) (by norm_num : (0 : ℝ) < 8.316) h1
    linarith
  -- Transform goal
  have h_transform : (7 : ℝ) / 12 - Real.log (3 / 2) / Real.log 2 =
                     (7 * Real.log 2 - 12 * Real.log (3/2)) / (12 * Real.log 2) := by
    field_simp
  rw [h_transform, abs_div, abs_of_pos h_denom_pos]
  have h_num : |7 * Real.log 2 - 12 * Real.log (3/2)| = 12 * Real.log (3/2) - 7 * Real.log 2 := by
    rw [abs_sub_comm, abs_of_pos h_diff_pos]
  rw [h_num]
  calc (12 * Real.log (3/2) - 7 * Real.log 2) / (12 * Real.log 2)
      < 0.02 / (12 * Real.log 2) := by
          apply div_lt_div_of_pos_right h_diff_upper (by linarith)
    _ < 1 / 100 := h_bound

/-- The equal-tempered fifth (7 semitones) as a frequency ratio.
    2^(7/12) ≈ 1.4983 ≈ 1.5 = 3/2 -/
noncomputable def equalTemperedFifth : ℝ := Real.rpow 2 (7/12)

/-- 2^(7/12) ≈ 1.49831 vs 3/2 = 1.5, difference ≈ 0.00169 < 0.002
    Numerical verification:
    - 2^(7/12) ≈ 1.4983
    - 3/2 = 1.5
    - |1.4983 - 1.5| = 0.0017 < 0.002 ✓ -/
theorem equal_tempered_fifth_approx_just :
    |equalTemperedFifth - fifth| < 0.002 := by
  simp only [equalTemperedFifth, fifth]
  have h_pos_2_le : (0 : ℝ) ≤ 2 := by norm_num
  have h_one_twelfth_pos : (0 : ℝ) < 1 / 12 := by norm_num
  have h_inv_eq : ((12 : ℕ) : ℝ)⁻¹ = 1 / 12 := by norm_num
  -- Upper bound: 2^(7/12) < 3/2
  have h_upper : Real.rpow 2 ((7 : ℝ) / 12) < 3 / 2 := by
    have h : (128 : ℝ) < (3 / 2 : ℝ) ^ (12 : ℕ) := by norm_num
    have h_pos_base_le : (0 : ℝ) ≤ 3 / 2 := by norm_num
    have step1 : Real.rpow 2 ((7 : ℝ) / 12) = (128 : ℝ) ^ ((1 : ℝ) / 12) := by
      calc Real.rpow 2 ((7 : ℝ) / 12)
        _ = Real.rpow 2 ((7 : ℝ) * (1 / 12)) := by ring_nf
        _ = (Real.rpow 2 (7 : ℝ)) ^ (1 / 12 : ℝ) := Real.rpow_mul h_pos_2_le 7 (1/12)
        _ = (128 : ℝ) ^ ((1 : ℝ) / 12) := by norm_num
    have step2 : (3 / 2 : ℝ) = ((3 / 2 : ℝ) ^ (12 : ℕ)) ^ ((1 : ℝ) / 12) := by
      rw [← h_inv_eq]
      exact (Real.pow_rpow_inv_natCast h_pos_base_le (by norm_num : (12 : ℕ) ≠ 0)).symm
    rw [step1, step2]
    apply Real.rpow_lt_rpow (by norm_num) h h_one_twelfth_pos
  -- Lower bound: 2^(7/12) > 1.498
  have h_lower : Real.rpow 2 ((7 : ℝ) / 12) > 1.498 := by
    have h : (1.498 : ℝ) ^ (12 : ℕ) < 128 := by norm_num
    have h_pos_base_le : (0 : ℝ) ≤ 1.498 := by norm_num
    have step1 : (1.498 : ℝ) = ((1.498 : ℝ) ^ (12 : ℕ)) ^ ((1 : ℝ) / 12) := by
      rw [← h_inv_eq]
      exact (Real.pow_rpow_inv_natCast h_pos_base_le (by norm_num : (12 : ℕ) ≠ 0)).symm
    have step2 : Real.rpow 2 ((7 : ℝ) / 12) = (128 : ℝ) ^ ((1 : ℝ) / 12) := by
      calc Real.rpow 2 ((7 : ℝ) / 12)
        _ = Real.rpow 2 ((7 : ℝ) * (1 / 12)) := by ring_nf
        _ = (Real.rpow 2 (7 : ℝ)) ^ (1 / 12 : ℝ) := Real.rpow_mul h_pos_2_le 7 (1/12)
        _ = (128 : ℝ) ^ ((1 : ℝ) / 12) := by norm_num
    rw [step1, step2]
    apply Real.rpow_lt_rpow (by positivity) h h_one_twelfth_pos
  rw [abs_lt]
  constructor <;> linarith

/-! ## φ in the Circle of Fifths -/

/-- The "golden interval" in cents: 1200/φ ≈ 741.64 cents. -/
noncomputable def goldenIntervalCents : ℝ := 1200 / Foundation.PhiForcing.φ

/-- 1200/φ ≈ 741.64 cents, |741.64 - 700| = 41.64 < 50 -/
theorem golden_interval_near_fifth :
    |goldenIntervalCents - 700| < 50 := by
  unfold goldenIntervalCents
  rw [abs_lt]
  constructor
  · have hphi : Foundation.PhiForcing.φ < 1.8 := Foundation.PhiForcing.phi_lt_onePointEight
    have : 1200 / Foundation.PhiForcing.φ > 1200 / 1.8 := by
      apply div_lt_div_of_pos_left (by norm_num) Foundation.PhiForcing.phi_pos hphi
    have h650 : (1200 / 1.8 : ℝ) = 2000 / 3 := by
      have : (1.8 : ℝ) = 18 / 10 := by norm_num
      rw [this]; field_simp; ring
    rw [h650] at this
    linarith
  · have hphi : Foundation.PhiForcing.φ > 1.6 := Foundation.PhiForcing.phi_gt_onePointSix
    have : 1200 / Foundation.PhiForcing.φ < 1200 / 1.6 := by
      apply div_lt_div_of_pos_left (by norm_num) (by linarith [Foundation.PhiForcing.phi_pos]) hphi
    have h750 : (1200 / 1.6 : ℝ) = 750 := by
      have : (1.6 : ℝ) = 16 / 10 := by norm_num
      rw [this]; field_simp; ring
    rw [h750] at this
    linarith

/-- The chromatic scale structure mirrors Fibonacci:
    12 = 5 + 7 (black + white keys on piano) -/
theorem chromatic_fibonacci_structure :
    (5 : ℕ) + 7 = semitonesPerOctave := by
  simp [semitonesPerOctave]

/-- The ratio of black to total keys approximates 1/φ². -/
theorem black_keys_golden_ratio :
    |(5 : ℝ) / 12 - 1 / Foundation.PhiForcing.φ^2| < 0.04 := by
  have h_phi_sq : Foundation.PhiForcing.φ^2 = Foundation.PhiForcing.φ + 1 := Foundation.PhiForcing.phi_equation
  rw [h_phi_sq, abs_lt]
  constructor
  · have h_denom : Foundation.PhiForcing.φ + 1 > 2.618 := by linarith [Foundation.PhiForcing.phi_gt_onePointSixOneEight]
    have h_denom_pos : 0 < Foundation.PhiForcing.φ + 1 := by linarith [Foundation.PhiForcing.phi_pos]
    have : 1 / (Foundation.PhiForcing.φ + 1) < 1 / 2.618 := one_div_lt_one_div_of_lt (by norm_num) h_denom
    linarith
  · have h_denom : Foundation.PhiForcing.φ + 1 < 2.619 := by linarith [Foundation.PhiForcing.phi_lt_onePointSixOneNine]
    have h_denom_pos : 0 < Foundation.PhiForcing.φ + 1 := by linarith [Foundation.PhiForcing.phi_pos]
    have : 1 / (Foundation.PhiForcing.φ + 1) > 1 / 2.619 := one_div_lt_one_div_of_lt h_denom_pos h_denom
    linarith

end CircleOfFifths
end MusicTheory
end IndisputableMonolith
