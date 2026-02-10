import Mathlib
open Complex

example (z : ℂ) (x : ℝ) : (z * (x:ℂ)).re = z.re * x := by
  simp [Complex.mul_re]

example (z : ℂ) (x : ℝ) : ((x:ℂ) * z).re = x * z.re := by
  simp [Complex.mul_re, mul_comm, mul_left_comm, mul_assoc]

