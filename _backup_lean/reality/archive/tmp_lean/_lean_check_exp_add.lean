import Mathlib

open Complex
open scoped Real

example (z w : ℂ) : Complex.exp (z + w) = Complex.exp z * Complex.exp w := by
  simpa using Complex.exp_add z w

example (z : ℂ) : Complex.exp (-z) = (Complex.exp z)⁻¹ := by
  simpa using Complex.exp_neg z
