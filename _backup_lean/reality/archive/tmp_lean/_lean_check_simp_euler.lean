import Mathlib

open Complex
open scoped Real

example (ω t : ℝ) : Complex.exp (-(Complex.I * (ω:ℂ) * (t:ℂ))) = Complex.exp (-( (t:ℂ) * (Complex.I * (ω:ℂ)))) := by
  ring_nf
