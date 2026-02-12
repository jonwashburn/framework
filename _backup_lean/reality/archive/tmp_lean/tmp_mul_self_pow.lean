import Mathlib

example (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  -- use mul_self_le_mul_self then simp
  have : a * a ≤ b * b := mul_self_le_mul_self ha hab
  simpa [pow_two] using this
