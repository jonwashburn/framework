import Mathlib

open Complex

example (x : ℝ) : (Complex.exp (((x:ℝ):ℂ) * Complex.I)).re = Real.cos x := by
  simpa using (Complex.exp_ofReal_mul_I_re x)

example (x : ℝ) : (Complex.exp (x * Complex.I)).re = Real.cos x := by
  -- here x is ℝ, coerced to ℂ in multiplication
  simpa using (Complex.exp_ofReal_mul_I_re x)

