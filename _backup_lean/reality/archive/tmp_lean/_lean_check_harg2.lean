import Mathlib

namespace Scratch

open scoped Real
open Complex

noncomputable section

example (τ ω t : ℝ) (hτ : τ ≠ 0) :
    (-( (t:ℂ) * ((1/τ:ℝ):ℂ) ) + -( (t:ℂ) * (Complex.I * (ω:ℂ))))
      = t • (-( ((1/τ:ℝ):ℂ) + Complex.I * (ω:ℂ))) := by
  simp [Algebra.smul_def, hτ]
  ring_nf

end

end Scratch
