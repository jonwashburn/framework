import Mathlib

open scoped Real
open Complex

namespace Scratch

noncomputable section

def aω (τ ω : ℝ) : ℂ := ((1/τ:ℝ):ℂ) + Complex.I * (ω:ℂ)

example (τ ω t : ℝ) :
    (-((t:ℂ) / (τ:ℂ)) + -( (t:ℂ) * (Complex.I * (ω:ℂ))))
      = t • (-(aω τ ω)) := by
  unfold aω
  simp [Algebra.smul_def, div_eq_mul_inv]
  ring_nf

end

end Scratch
