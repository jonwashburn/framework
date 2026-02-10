import Mathlib

namespace Scratch

open scoped Real
open Complex

noncomputable section

-- direct integrand equality
example (Δ τ ω t : ℝ) :
    ((Δ/τ) * Real.exp (-t/τ) : ℝ)
      = (Δ/τ) * Real.exp (-t/τ) := by
  ring

-- core complex rewrite
example (Δ τ ω t : ℝ) (hτ : τ ≠ 0) :
    (((Δ/τ) * Real.exp (-t/τ) : ℝ) : ℂ) * Complex.exp (-(Complex.I * (ω:ℂ) * (t:ℂ)))
      = ((Δ/τ : ℝ) : ℂ) * Complex.exp (t • (-( ((1/τ:ℝ):ℂ) + Complex.I * (ω:ℂ)))) := by
  -- expand the kernel and pull out constants
  -- LHS = (Δ/τ) * (↑(Real.exp (-t/τ)) : ℂ) * exp(-i ω t)
  have : (((Δ/τ) * Real.exp (-t/τ) : ℝ) : ℂ)
            = ((Δ/τ : ℝ) : ℂ) * (↑(Real.exp (-t/τ)) : ℂ) := by
    simp [mul_assoc]
  -- use this and then the earlier rewrite for exp(-t/τ)*exp(-iωt)
  calc
    (((Δ/τ) * Real.exp (-t/τ) : ℝ) : ℂ) * Complex.exp (-(Complex.I * (ω:ℂ) * (t:ℂ)))
        = ((Δ/τ : ℝ) : ℂ) * (↑(Real.exp (-t/τ)) : ℂ) * Complex.exp (-(Complex.I * (ω:ℂ) * (t:ℂ))) := by
            simp [this, mul_assoc]
    _ = ((Δ/τ : ℝ) : ℂ) * (Complex.exp (↑(-t/τ : ℝ))) * Complex.exp (-(Complex.I * (ω:ℂ) * (t:ℂ))) := by
            simp [Complex.ofReal_exp, mul_assoc]
    _ = ((Δ/τ : ℝ) : ℂ) * Complex.exp ((↑(-t/τ : ℝ) : ℂ) + (-(Complex.I * (ω:ℂ) * (t:ℂ)))) := by
            -- regroup and use exp_add backwards
            simp [mul_assoc, ← Complex.exp_add (↑(-t/τ : ℝ) : ℂ) (-(Complex.I * (ω:ℂ) * (t:ℂ)))]
    _ = ((Δ/τ : ℝ) : ℂ) * Complex.exp (t • (-( ((1/τ:ℝ):ℂ) + Complex.I * (ω:ℂ)))) := by
            -- normalize the exponent
            have harg : (↑(-t/τ : ℝ) : ℂ) + (-(Complex.I * (ω:ℂ) * (t:ℂ)))
                    = t • (-( ((1/τ:ℝ):ℂ) + Complex.I * (ω:ℂ))) := by
              simp [Algebra.smul_def, hτ]
              ring_nf
            simp [harg]

end

end Scratch
