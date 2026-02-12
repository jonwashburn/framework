import Mathlib

namespace Scratch

open scoped Real
open Complex

noncomputable section

def aω (τ ω : ℝ) : ℂ := ((1/τ:ℝ):ℂ) + Complex.I * (ω:ℂ)

example (Δ τ ω t : ℝ) (hτ : τ ≠ 0) :
    (((Δ/τ) * Real.exp (-t/τ) : ℝ) : ℂ) * Complex.exp (-(Complex.I * (ω:ℂ) * (t:ℂ)))
      = ((Δ/τ : ℝ) : ℂ) * Complex.exp (t • (-(aω τ ω))) := by
  have hker : (((Δ/τ) * Real.exp (-t/τ) : ℝ) : ℂ)
      = ((Δ/τ : ℝ) : ℂ) * (↑(Real.exp (-t/τ)) : ℂ) := by
    simp [mul_assoc]
  have h1 : (↑(Real.exp (-t/τ)) : ℂ) = Complex.exp (↑(-t/τ : ℝ)) := by
    simpa using (Complex.ofReal_exp (-t/τ))
  have hi : Complex.exp (-(Complex.I * (ω:ℂ) * (t:ℂ)))
            = Complex.exp (-( (t:ℂ) * (Complex.I * (ω:ℂ)))) := by
    ring_nf
  have hexp_mul :
      Complex.exp (↑(-t/τ : ℝ)) * Complex.exp (-( (t:ℂ) * (Complex.I * (ω:ℂ))))
        = Complex.exp ((↑(-t/τ : ℝ) : ℂ) + (-( (t:ℂ) * (Complex.I * (ω:ℂ))))) := by
    simpa using (Eq.symm (Complex.exp_add (↑(-t/τ : ℝ) : ℂ) (-( (t:ℂ) * (Complex.I * (ω:ℂ))))))
  have harg : (↑(-t/τ : ℝ) : ℂ) + (-( (t:ℂ) * (Complex.I * (ω:ℂ))))
        = t • (-(aω τ ω)) := by
    unfold aω
    simp [Algebra.smul_def, hτ]
    ring_nf

  calc
    (((Δ/τ) * Real.exp (-t/τ) : ℝ) : ℂ) * Complex.exp (-(Complex.I * (ω:ℂ) * (t:ℂ)))
        = ((Δ/τ : ℝ) : ℂ) * (↑(Real.exp (-t/τ)) : ℂ) * Complex.exp (-(Complex.I * (ω:ℂ) * (t:ℂ))) := by
            simp [hker, mul_assoc]
    _ = ((Δ/τ : ℝ) : ℂ) * (Complex.exp (↑(-t/τ : ℝ))) * Complex.exp (-(Complex.I * (ω:ℂ) * (t:ℂ))) := by
            simp [h1, mul_assoc]
    _ = ((Δ/τ : ℝ) : ℂ) * (Complex.exp (↑(-t/τ : ℝ))) * Complex.exp (-( (t:ℂ) * (Complex.I * (ω:ℂ)))) := by
            simp [hi]
    _ = ((Δ/τ : ℝ) : ℂ) * (Complex.exp (↑(-t/τ : ℝ)) * Complex.exp (-( (t:ℂ) * (Complex.I * (ω:ℂ))))) := by
            simp [mul_assoc]
    _ = ((Δ/τ : ℝ) : ℂ) * Complex.exp ((↑(-t/τ : ℝ) : ℂ) + (-( (t:ℂ) * (Complex.I * (ω:ℂ))))) := by
            -- rewrite inside without cancelling
            congr 1
            exact hexp_mul
    _ = ((Δ/τ : ℝ) : ℂ) * Complex.exp (t • (-(aω τ ω))) := by
            -- rewrite exponent without cancelling
            congr 1
            simpa [harg]

end

end Scratch
