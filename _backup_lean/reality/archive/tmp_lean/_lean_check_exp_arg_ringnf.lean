import Mathlib

open Complex

example (τ ω t : ℝ) (hτ : τ ≠ 0) :
    Complex.exp (-((t:ℂ) / (τ:ℂ)) + -(Complex.I * (ω:ℂ) * (t:ℂ)))
      = Complex.exp (-( (t:ℂ) * (Complex.I * (ω:ℂ))) + -( (t:ℂ) * ((τ:ℂ)⁻¹))) := by
  -- reduce to equality of arguments
  have : (-((t:ℂ) / (τ:ℂ)) + -(Complex.I * (ω:ℂ) * (t:ℂ)))
        = (-( (t:ℂ) * (Complex.I * (ω:ℂ))) + -( (t:ℂ) * ((τ:ℂ)⁻¹))) := by
    -- rewrite division
    simp [div_eq_mul_inv]
    ring_nf
  simpa [this]
