import Mathlib

#check Complex.norm_ofReal
#check (Complex.norm_ofReal (Real.sqrt 8))

example : ‖(Real.sqrt 8 : ℂ)‖ = Real.sqrt 8 := by
  have h : (0 : ℝ) ≤ Real.sqrt 8 := le_of_lt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 8))
  -- try simp without naming the lemma
  simp [abs_of_nonneg h]
