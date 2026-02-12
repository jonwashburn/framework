import Mathlib

namespace Scratch

open scoped Real
open Complex

noncomputable section

example (Δ τ ω t : ℝ) (hτ : τ ≠ 0) :
    (((Δ/τ) * Real.exp (-t/τ) : ℝ) : ℂ) * Complex.exp (-(Complex.I * (ω:ℂ) * (t:ℂ)))
      = ((Δ/τ : ℝ) : ℂ) * Complex.exp (t • (-( ((1/τ:ℝ):ℂ) + Complex.I * (ω:ℂ)))) := by
  have hker : (((Δ/τ) * Real.exp (-t/τ) : ℝ) : ℂ)
      = ((Δ/τ : ℝ) : ℂ) * (↑(Real.exp (-t/τ)) : ℂ) := by
    simp [mul_assoc]

  have h1 : (↑(Real.exp (-t/τ)) : ℂ) = Complex.exp (↑(-t/τ : ℝ)) := by
    simpa using (Complex.ofReal_exp (-t/τ))

  have harg : (↑(-t/τ : ℝ) : ℂ) + (-(Complex.I * (ω:ℂ) * (t:ℂ)))
        = t • (-( ((1/τ:ℝ):ℂ) + Complex.I * (ω:ℂ))) := by
    simp [Algebra.smul_def, hτ]
    ring_nf

  calc
    (((Δ/τ) * Real.exp (-t/τ) : ℝ) : ℂ) * Complex.exp (-(Complex.I * (ω:ℂ) * (t:ℂ)))
        = ((Δ/τ : ℝ) : ℂ) * (↑(Real.exp (-t/τ)) : ℂ) * Complex.exp (-(Complex.I * (ω:ℂ) * (t:ℂ))) := by
            simp [hker, mul_assoc]
    _ = ((Δ/τ : ℝ) : ℂ) * (Complex.exp (↑(-t/τ : ℝ))) * Complex.exp (-(Complex.I * (ω:ℂ) * (t:ℂ))) := by
            simp [h1, mul_assoc]
    _ = ((Δ/τ : ℝ) : ℂ) * ((Complex.exp (↑(-t/τ : ℝ))) * Complex.exp (-(Complex.I * (ω:ℂ) * (t:ℂ)))) := by
            simp [mul_assoc]
    _ = ((Δ/τ : ℝ) : ℂ) * Complex.exp ((↑(-t/τ : ℝ) : ℂ) + (-(Complex.I * (ω:ℂ) * (t:ℂ)))) := by
            congr 1
            simpa using (Eq.symm (Complex.exp_add (↑(-t/τ : ℝ) : ℂ) (-(Complex.I * (ω:ℂ) * (t:ℂ)))))
    _ = ((Δ/τ : ℝ) : ℂ) * Complex.exp (t • (-( ((1/τ:ℝ):ℂ) + Complex.I * (ω:ℂ)))) := by
            simp [harg]

end

end Scratch
