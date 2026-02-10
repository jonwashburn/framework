import Mathlib

open scoped Real
open Complex

namespace Scratch

noncomputable section

example (Δ τ ω t : ℝ) (hτ : τ ≠ 0) :
    ((Δ/τ : ℝ) : ℂ) * Complex.exp (-((t:ℂ) / (τ:ℂ)) + -(Complex.I * (ω:ℂ) * (t:ℂ)))
      = ((Δ/τ : ℝ) : ℂ) * Complex.exp (-( (t:ℂ) * (Complex.I * (ω:ℂ))) + -( (t:ℂ) * ((τ:ℂ)⁻¹))) := by
  congr 1
  have : (-((t:ℂ) / (τ:ℂ)) + -(Complex.I * (ω:ℂ) * (t:ℂ)))
        = (-( (t:ℂ) * (Complex.I * (ω:ℂ))) + -( (t:ℂ) * ((τ:ℂ)⁻¹))) := by
    simp [div_eq_mul_inv]
    ring_nf
  simpa [this]

end

end Scratch
