import Mathlib

open scoped BigOperators

example (a b : ℝ) (h9 : (9:ℝ) * b ≤ a) : (0.9:ℝ) * (a + b) ≤ a := by
  -- direct algebra
  nlinarith
