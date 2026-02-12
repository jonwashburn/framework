import Mathlib

example : ‖(Real.sqrt 8 : ℂ)‖ = Real.sqrt 8 := by
  have h : (0 : ℝ) ≤ Real.sqrt 8 := le_of_lt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 8))
  have : ‖(Real.sqrt 8 : ℂ)‖ = |Real.sqrt 8| := by
    simpa using (RCLike.norm_ofReal (K := ℂ) (Real.sqrt 8))
  simpa [abs_of_nonneg h] using this
