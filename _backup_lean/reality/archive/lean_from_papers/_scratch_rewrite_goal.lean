import Mathlib

variable (S : ℂ)

example : ((‖S‖ / |Real.sqrt 8|) ^ 2 : ℝ) = (‖S‖ ^ 2) / 8 := by
  have hsqrt8_nonneg : (0 : ℝ) ≤ Real.sqrt 8 := by
    exact le_of_lt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 8))
  have habs : |Real.sqrt 8| = Real.sqrt 8 := abs_of_nonneg hsqrt8_nonneg
  have hsq : (Real.sqrt 8)^2 = (8 : ℝ) := by
    simpa using (Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 8))
  rw [div_pow]
  simp [habs, hsq, pow_two, mul_assoc, mul_left_comm, mul_comm]
