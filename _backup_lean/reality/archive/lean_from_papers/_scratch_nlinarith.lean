import Mathlib

example : (1/8 : ℝ) < (2 - Real.sqrt 2) / 4 := by
  have hs : Real.sqrt 2 < (3/2 : ℝ) := Real.sqrt_two_lt_three_halves
  nlinarith [hs]
