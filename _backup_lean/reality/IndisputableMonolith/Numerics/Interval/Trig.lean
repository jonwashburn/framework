import IndisputableMonolith.Numerics.Interval.Basic
import IndisputableMonolith.Numerics.Interval.PiBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Interval Arithmetic for Trigonometric Functions

This module provides rigorous interval bounds for arctan and tan.
-/

namespace IndisputableMonolith.Numerics

open Interval
open Real
open Filter
open scoped Topology Finset

/-- Taylor series for arctan(x) up to n terms: sum_{i=0}^{n-1} (-1)^i x^(2i+1)/(2i+1) -/
noncomputable def arctanTaylor (n : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, ((-1 : ℝ) ^ i * x ^ (2 * i + 1)) / (2 * (i : ℝ) + 1)

/-- Error bound for arctan Taylor series for 0 < x < 1. -/
theorem arctan_taylor_error {x : ℝ} (hx_pos : 0 < x) (hx_le : x < 1) (n : ℕ) :
    |arctan x - arctanTaylor n x| ≤ x ^ (2 * n + 1) / (2 * (n : ℝ) + 1) := by
  let f := fun (i : ℕ) => x ^ (2 * i + 1) / (2 * (i : ℝ) + 1)
  have h_hasSum := Real.hasSum_arctan (hx := by rw [norm_eq_abs, abs_of_pos hx_pos]; exact hx_le)
  have h_tsum : arctan x = ∑' i : ℕ, ((-1 : ℝ) ^ i * x ^ (2 * i + 1)) / (2 * (i : ℝ) + 1) := h_hasSum.tsum_eq

  -- We need to prove that f is antitone and summable.
  have h_summable : Summable f := by
    apply Summable.of_nonneg_of_le (f := fun i => (x^2)^i * x)
    · intro i; unfold f; positivity
    · intro i; unfold f
      have h_denom : 1 ≤ (2 * (i : ℝ) + 1) := by norm_cast; linarith
      rw [div_le_iff₀ (by linarith)]
      nth_rw 1 [← mul_one (x ^ (2 * i + 1))]
      have h_pow : x ^ (2 * i + 1) = (x^2)^i * x := by
        rw [pow_succ, pow_mul]; rfl
      rw [h_pow]
      apply mul_le_mul_of_nonneg_left
      · linarith
      · positivity
    · apply Summable.mul_right
      apply summable_geometric_of_lt_one (h₁ := sq_nonneg x) (h₂ := pow_lt_one₀ (hx_pos.le) hx_le (by norm_num))

  have h_anti : Antitone f := by
    intro i j hij
    unfold f
    apply div_le_div
    · positivity
    · apply pow_le_pow_of_le_one hx_pos.le hx_le.le
      linarith
    · linarith
    · linarith

  have h_error := alternating_series_error_bound f h_anti h_summable n
  rw [h_tsum]
  unfold arctanTaylor
  -- Match the summation index and terms
  have h_func : (fun i => (-1 : ℝ) ^ i * x ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) = (fun i => (-1 : ℝ) ^ i * f i) := by
    ext i; unfold f; ring
  simp_rw [h_func]
  exact h_error

/-- Interval containing arctan(1/3) ≈ 0.32175 -/
def arctanOneThirdInterval : Interval where
  lo := 321 / 1000  -- 0.321
  hi := 322 / 1000  -- 0.322
  valid := by norm_num

/-- arctan(1/3) is in arctanOneThirdInterval -/
theorem arctan_one_third_in_interval : arctanOneThirdInterval.contains (arctan (1/3)) := by
  simp only [contains, arctanOneThirdInterval]
  let x := (1/3 : ℝ)
  have hx_pos : 0 < x := by norm_num
  have hx_le : x < 1 := by norm_num
  have h_bound := arctan_taylor_error hx_pos hx_le 3
  unfold arctanTaylor at h_bound
  -- S_3 = x - x^3/3 + x^5/5 = 1/3 - 1/81 + 1/1215 = 391/1215
  have h_sum_eq : (∑ i ∈ Finset.range 3, (-1 : ℝ) ^ i * x ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) = 391/1215 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
    ring
  rw [h_sum_eq] at h_bound
  have h_err_val : x ^ (2 * 3 + 1) / (2 * (3 : ℝ) + 1) = 1/15309 := by
    norm_num
    ring
  rw [h_err_val] at h_bound
  rw [abs_sub_le_iff] at h_bound
  constructor
  · -- 0.321 ≤ arctan(1/3)
    calc (321 / 1000 : ℝ) = 321/1000 := by norm_num
      _ ≤ 391/1215 - 1/15309 := by norm_num
      _ ≤ arctan (1/3) := h_bound.1
  · -- arctan(1/3) ≤ 0.322
    calc arctan (1/3) ≤ 391/1215 + 1/15309 := h_bound.2
      _ ≤ 322/1000 := by norm_num
      _ = (322 / 1000 : ℝ) := by norm_num

/-- Interval containing arctan 2 = pi/4 + arctan(1/3) -/
def arctanTwoInterval : Interval :=
  let pi4 := smulPos (1 / 4) piInterval (by norm_num)
  add pi4 arctanOneThirdInterval

theorem arctan_two_in_interval : arctanTwoInterval.contains (arctan 2) := by
  have h_pi_in : piInterval.contains Real.pi := pi_in_piInterval

  have h_at2_eq : arctan 2 = Real.pi / 4 + arctan (1 / 3) := by
    rw [← arctan_one]
    have h_lt : (1 : ℝ) * (1 / 3) < 1 := by norm_num
    rw [arctan_add h_lt]
    congr; field_simp; ring

  rw [h_at2_eq]
  unfold arctanTwoInterval Interval.add Interval.smulPos
  apply add_contains_add
  · have h_eq : Real.pi / 4 = (1 / 4 : ℝ) * Real.pi := by ring
    rw [h_eq]
    apply smulPos_contains_smul
    · norm_num
    · exact h_pi_in
  · exact arctan_one_third_in_interval

end IndisputableMonolith.Numerics
