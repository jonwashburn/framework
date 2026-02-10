import Mathlib
import Mathlib.NumberTheory.Real.GoldenRatio
import IndisputableMonolith.Constants

namespace IndisputableMonolith
namespace Support

open Real

/-- φ = (1 + √5) / 2 = goldenRatio. -/
private lemma phi_eq : Constants.phi = goldenRatio := rfl

/-- Coarse bounds on φ: 1.6 < φ < 1.7.
    Proof uses tighter √5 bounds: 2.23 < √5 < 2.24 gives better control. -/
theorem phi_bounds_stub : (1.6 : ℝ) < Constants.phi ∧ Constants.phi < 1.7 := by
  -- Use tighter bounds: 2.23 < √5 < 2.24
  have hsqrt5_lower : (2.23 : ℝ) < Real.sqrt 5 := by
    have h : (2.23 : ℝ) ^ 2 < 5 := by norm_num
    have h_pos : 0 ≤ (2.23 : ℝ) := by norm_num
    calc 2.23 = Real.sqrt (2.23 ^ 2) := (Real.sqrt_sq h_pos).symm
      _ < Real.sqrt 5 := Real.sqrt_lt_sqrt (by norm_num) h
  have hsqrt5_upper : Real.sqrt 5 < (2.24 : ℝ) := by
    have h : 5 < (2.24 : ℝ) ^ 2 := by norm_num
    have h_pos : 0 ≤ (2.24 : ℝ) := by norm_num
    calc Real.sqrt 5 < Real.sqrt (2.24 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) h
      _ = 2.24 := Real.sqrt_sq h_pos
  constructor
  · -- 1.6 < φ
    -- (1 + 2.23) / 2 = 3.23 / 2 = 1.615 > 1.6
    have h1 : (1.6 : ℝ) < (1 + 2.23) / 2 := by norm_num
    have h2 : (1 + 2.23 : ℝ) / 2 ≤ (1 + Real.sqrt 5) / 2 := by
      have hpos : (0 : ℝ) < 2 := by norm_num
      exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hpos)
    have h3 : (1 + Real.sqrt 5) / 2 = Constants.phi := by simp [Constants.phi]
    linarith
  · -- φ < 1.7
    -- (1 + 2.24) / 2 = 3.24 / 2 = 1.62 < 1.7
    have h1 : Constants.phi = (1 + Real.sqrt 5) / 2 := by simp [Constants.phi]
    have h2 : (1 + Real.sqrt 5 : ℝ) / 2 < (1 + 2.24) / 2 := by
      have hpos : (0 : ℝ) < 2 := by norm_num
      exact div_lt_div_of_pos_right (by linarith) hpos
    have h3 : (1 + 2.24 : ℝ) / 2 < 1.7 := by norm_num
    rw [h1]; linarith

end Support
end IndisputableMonolith
