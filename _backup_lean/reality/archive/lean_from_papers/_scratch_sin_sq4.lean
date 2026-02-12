import Mathlib

open Real

example : (Real.sin (Real.pi/8))^2 = (2 - Real.sqrt 2) / 4 := by
  have hs : Real.sqrt 2 < (3/2 : ℝ) := Real.sqrt_two_lt_three_halves
  have hnonneg : 0 ≤ (2 - Real.sqrt 2) := by nlinarith [hs]
  rw [Real.sin_pi_div_eight]
  -- (√(2-√2)/2)^2 = (2-√2)/4
  -- use (a/b)^2 = a^2/b^2
  -- then simplify 2^2 = 4
  simp [div_pow, Real.sq_sqrt hnonneg, pow_two]
