import Mathlib

example : ‖(Real.sqrt 8 : ℂ)‖ = Real.sqrt 8 := by
  -- norm of a nonnegative real in ℂ is itself
  have h : (0 : ℝ) ≤ Real.sqrt 8 := le_of_lt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 8))
  -- `Complex.norm_ofReal` gives |x|
  simpa [Complex.norm_ofReal, abs_of_nonneg h]
