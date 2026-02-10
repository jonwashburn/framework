import Mathlib

open Complex

example (t τ : ℝ) : (t:ℂ) / (τ:ℂ) = (t:ℂ) * ((τ:ℂ)⁻¹) := by
  simp [div_eq_mul_inv]
