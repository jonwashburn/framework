import Mathlib

example (z : ℂ) : Complex.normSq z = ‖z‖ * ‖z‖ := by
  simpa [Complex.normSq_eq_norm_sq, pow_two]
