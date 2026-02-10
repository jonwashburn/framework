import Mathlib

open scoped Real
open Complex

namespace Scratch

noncomputable section

def aω (τ ω : ℝ) : ℂ := ((1/τ:ℝ):ℂ) + Complex.I * (ω:ℂ)

example (τ ω t : ℝ) (hτ : τ ≠ 0) :
    Complex.exp (t • (-(aω τ ω)))
      = Complex.exp (-( (t:ℂ) * ((1/τ:ℝ):ℂ) ) + -( (t:ℂ) * (Complex.I * (ω:ℂ)))) := by
  unfold aω
  simp [Algebra.smul_def, hτ]
  ring_nf

end

end Scratch
