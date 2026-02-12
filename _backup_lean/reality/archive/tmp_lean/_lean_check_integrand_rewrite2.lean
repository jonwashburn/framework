import Mathlib

namespace Scratch

open scoped Real
open Complex

noncomputable section

example (Δ τ ω t : ℝ) (hτ : τ ≠ 0) :
    ((Δ / τ : ℝ) : ℂ) * (↑(Real.exp (-t / τ)) : ℂ) * Complex.exp (-(Complex.I * (ω:ℂ) * (t:ℂ)))
      = ((Δ / τ : ℝ) : ℂ) * Complex.exp (t • (-( ((1/τ:ℝ):ℂ) + Complex.I * (ω:ℂ)))) := by
  -- factor out constant
  -- focus on the exponential product
  have h1 : (↑(Real.exp (-t / τ)) : ℂ) = Complex.exp (↑(-t / τ : ℝ)) := by
    simpa using (Complex.ofReal_exp (-t/τ))

  -- show the product of exponentials equals exp of sum
  calc
    ((Δ / τ : ℝ) : ℂ) * (↑(Real.exp (-t / τ)) : ℂ) * Complex.exp (-(Complex.I * (ω:ℂ) * (t:ℂ)))
        = ((Δ / τ : ℝ) : ℂ) * (Complex.exp (↑(-t / τ : ℝ))) * Complex.exp (-(Complex.I * (ω:ℂ) * (t:ℂ))) := by
            simp [h1, mul_assoc]
    _ = ((Δ / τ : ℝ) : ℂ) * Complex.exp ((↑(-t / τ : ℝ) : ℂ) + (-(Complex.I * (ω:ℂ) * (t:ℂ)))) := by
            -- exp_add, then reassociate
            simp [Complex.exp_add, mul_assoc]
    _ = ((Δ / τ : ℝ) : ℂ) * Complex.exp (t • (-( ((1/τ:ℝ):ℂ) + Complex.I * (ω:ℂ)))) := by
            -- simplify the exponent
            -- unfold smul and normalize
            have : (↑(-t / τ : ℝ) : ℂ) + (-(Complex.I * (ω:ℂ) * (t:ℂ)))
                = t • (-( ((1/τ:ℝ):ℂ) + Complex.I * (ω:ℂ))) := by
              -- unfold smul as multiplication by ofReal
              simp [Algebra.smul_def, hτ]
              ring_nf
            simp [this]

end

end Scratch
