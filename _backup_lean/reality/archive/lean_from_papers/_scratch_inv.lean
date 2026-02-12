import Mathlib

example (x : ℝ) : x⁻¹ = 1/x := by
  simp [div_eq_mul_inv]
