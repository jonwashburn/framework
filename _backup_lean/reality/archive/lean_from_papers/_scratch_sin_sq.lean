import Mathlib

open Real

example : (Real.sin (Real.pi/8))^2 = (2 - Real.sqrt 2) / 4 := by
  -- use sin_pi_div_eight
  rw [Real.sin_pi_div_eight]
  -- (√(2-√2)/2)^2 = (2-√2)/4
  -- simplify
  have hnonneg : 0 ≤ (2 - Real.sqrt 2) := by
    have hs : Real.sqrt 2 < (3/2 : ℝ) := Real.sqrt_two_lt_three_halves
    nlinarith [hs]
  -- now
  -- expand square
  simp [pow_two, div_pow, Real.sq_sqrt hnonneg]
