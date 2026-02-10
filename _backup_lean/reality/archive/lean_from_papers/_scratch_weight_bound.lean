import Mathlib
import IndisputableMonolith.Constants.GapWeight.Formula
import IndisputableMonolith.Numerics.Interval.PhiBounds

namespace IndisputableMonolith.Constants.GapWeight

open scoped BigOperators
open IndisputableMonolith.Numerics

lemma sin_sq_pi_div_eight_gt_one_eighth : (1/8 : ℝ) < (Real.sin (Real.pi/8))^2 := by
  have hs : Real.sqrt 2 < (3/2 : ℝ) := Real.sqrt_two_lt_three_halves
  have h : (1/8 : ℝ) < (2 - Real.sqrt 2) / 4 := by
    nlinarith [hs]
  have hnonneg : 0 ≤ (2 - Real.sqrt 2) := by
    nlinarith [hs]
  have hsin_sq : (Real.sin (Real.pi/8))^2 = (2 - Real.sqrt 2) / 4 := by
    rw [Real.sin_pi_div_eight]
    rw [div_pow]
    rw [Real.sq_sqrt hnonneg]
    norm_num
  simpa [hsin_sq.symm] using h

lemma geometricWeight_one_gt_007725 : (0.07725 : ℝ) < geometricWeight (1 : Fin 8) := by
  have hk : (1 : Fin 8).val ≠ 0 := by decide
  have hsin : (1/8 : ℝ) < (Real.sin (Real.pi/8))^2 := sin_sq_pi_div_eight_gt_one_eighth
  have hphi : (0.618 : ℝ) < phi⁻¹ := by
    have h : (0.618 : ℝ) < Real.goldenRatio⁻¹ := Numerics.phi_inv_gt
    simpa [IndisputableMonolith.Constants.phi] using h
  have hconst : (0.07725 : ℝ) = (1/8 : ℝ) * (0.618 : ℝ) := by norm_num
  unfold geometricWeight
  simp [hk]
  -- rewrite phi^(-1) as phi⁻¹
  have hpow : (phi : ℝ) ^ (-(1 : ℤ)) = phi⁻¹ := by
    simpa using (zpow_neg_one (phi : ℝ))
  -- compare products
  have hprod : (1/8 : ℝ) * (0.618 : ℝ) < (Real.sin (Real.pi/8))^2 * (phi : ℝ) ^ (-(1 : ℤ)) := by
    have h0 : (0 : ℝ) ≤ (1/8 : ℝ) := by norm_num
    have h1 : (0 : ℝ) ≤ (0.618 : ℝ) := by norm_num
    have hphi' : (0.618 : ℝ) < (phi : ℝ) ^ (-(1 : ℤ)) := by
      simpa [hpow] using hphi
    exact mul_lt_mul'' hsin hphi' h0 h1
  simpa [hconst] using hprod

end IndisputableMonolith.Constants.GapWeight
