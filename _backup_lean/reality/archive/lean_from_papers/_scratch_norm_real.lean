import Mathlib

example (x : ℝ) : ‖(x : ℂ)‖ = |x| := by
  simpa using (Complex.norm_ofReal x)
