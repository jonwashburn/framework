import Mathlib

namespace Scratch

open scoped Real
open Complex

noncomputable section

-- A clean integrand rewrite that avoids simp-cancellation by using `congr 1` when needed.

def aω (τ ω : ℝ) : ℂ := ((1/τ:ℝ):ℂ) + Complex.I * (ω:ℂ)

example (Δ τ ω t : ℝ) (hτ : τ ≠ 0) :
    (((Δ/τ) * Real.exp (-t/τ) : ℝ) : ℂ) * Complex.exp (-(Complex.I * (ω:ℂ) * (t:ℂ)))
      = ((Δ/τ : ℝ) : ℂ) * Complex.exp (t • (-(aω τ ω))) := by
  -- expand cast of the real kernel
  have hker : (((Δ/τ) * Real.exp (-t/τ) : ℝ) : ℂ)
      = ((Δ/τ : ℝ) : ℂ) * (↑(Real.exp (-t/τ)) : ℂ) := by
    simp [mul_assoc]

  -- convert Real.exp to Complex.exp
  have h1 : (↑(Real.exp (-t/τ)) : ℂ) = Complex.exp (↑(-t/τ : ℝ)) := by
    simpa using (Complex.ofReal_exp (-t/τ))

  -- rewrite exp(-i ω t) argument into a commuted form
  have hi : Complex.exp (-(Complex.I * (ω:ℂ) * (t:ℂ)))
            = Complex.exp (-( (t:ℂ) * (Complex.I * (ω:ℂ)))) := by
    -- commutativity/associativity in ℂ
    ring_nf

  -- combine exponentials: exp(r) * exp(s) = exp(r+s)
  have hexp_mul :
      Complex.exp (↑(-t/τ : ℝ)) * Complex.exp (-( (t:ℂ) * (Complex.I * (ω:ℂ))))
        = Complex.exp ((↑(-t/τ : ℝ) : ℂ) + (-( (t:ℂ) * (Complex.I * (ω:ℂ))))) := by
    simpa using (Eq.symm (Complex.exp_add (↑(-t/τ : ℝ) : ℂ) (-( (t:ℂ) * (Complex.I * (ω:ℂ))))))

  -- normalize the exponent into the `t • (-(aω τ ω))` form
  have harg : (↑(-t/τ : ℝ) : ℂ) + (-( (t:ℂ) * (Complex.I * (ω:ℂ))))
        = t • (-(aω τ ω)) := by
    unfold aω
    simp [Algebra.smul_def, hτ]
    ring_nf

  -- assemble
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
            -- rewrite inside, without cancelling the prefactor
            congr 1
            simpa [hexp_mul]
    _ = ((Δ/τ : ℝ) : ℂ) * Complex.exp (t • (-(aω τ ω))) := by
            simp [harg]

end

end Scratch
