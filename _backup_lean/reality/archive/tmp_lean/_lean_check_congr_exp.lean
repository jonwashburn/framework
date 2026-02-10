import Mathlib

open scoped Real
open Complex

namespace Scratch

noncomputable section

example (Δ τ ω t : ℝ) (hτ : τ ≠ 0) :
    ((Δ/τ : ℝ) : ℂ) * Complex.exp ((↑(-t/τ : ℝ) : ℂ) + (-(Complex.I * (ω:ℂ) * (t:ℂ))))
      = ((Δ/τ : ℝ) : ℂ) * Complex.exp (t • (-( ((1/τ:ℝ):ℂ) + Complex.I * (ω:ℂ)))) := by
  have harg : (↑(-t/τ : ℝ) : ℂ) + (-(Complex.I * (ω:ℂ) * (t:ℂ)))
        = t • (-( ((1/τ:ℝ):ℂ) + Complex.I * (ω:ℂ))) := by
    simp [Algebra.smul_def, hτ]
    ring_nf
  -- prevent cancellation: rewrite only inside exp
  congr 1
  -- now goal is exp(arg1)=exp(arg2)
  -- use harg
  simpa [harg]

end

end Scratch
