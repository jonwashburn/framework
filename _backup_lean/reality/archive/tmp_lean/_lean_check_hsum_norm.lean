import Mathlib

namespace Scratch

open scoped Real
open Complex

noncomputable section

example (τ ω t : ℝ) (hτ : τ ≠ 0) :
    Complex.exp ((↑(-t / τ : ℝ) : ℂ) + (-(Complex.I * (ω:ℂ) * (t:ℂ))))
      = Complex.exp (t • (-( ((1/τ:ℝ):ℂ) + Complex.I * (ω:ℂ)))) := by
  -- prove equality of exponents
  have harg : (↑(-t / τ : ℝ) : ℂ) + (-(Complex.I * (ω:ℂ) * (t:ℂ)))
        = t • (-( ((1/τ:ℝ):ℂ) + Complex.I * (ω:ℂ))) := by
    simp [Algebra.smul_def, hτ]
    ring_nf
  -- now rewrite
  simpa [harg]

end

end Scratch
