import Mathlib

namespace Scratch

open scoped Real
open Complex

noncomputable section

-- Try to rewrite the Debye kernel integrand into a single complex exponential.

def τ : ℝ := 2

def Δ : ℝ := 3

def ω : ℝ := 5

example (t : ℝ) (hτ : 0 < τ) :
    ((Δ / τ) * Real.exp (-t / τ) : ℝ) * (Real.cos (ω*t)) = ((Δ / τ) * Real.exp (-t / τ)) * Real.cos (ω*t) := by
  ring

-- Complex form: exp(-t/τ) * exp(-i ω t) = exp(t • (-( (1/τ)+ i ω)))
example (t τ ω : ℝ) (hτ : τ ≠ 0) :
    ((Real.exp (-t / τ) : ℝ) : ℂ) * Complex.exp (-(Complex.I * (ω:ℂ) * (t:ℂ)))
      = Complex.exp (t • (-( ((1/τ:ℝ):ℂ) + Complex.I * (ω:ℂ)))) := by
  -- convert Real.exp to Complex.exp
  have h1 : ((Real.exp (-t / τ) : ℝ) : ℂ) = Complex.exp (↑(-t / τ : ℝ)) := by
    simpa using (Complex.ofReal_exp (-t/τ))
  -- rewrite RHS into exp(sum) and then use exp_add
  -- show: ↑(-t/τ) + (-(I*ω*t)) = t • (-( (1/τ)+I*ω))
  have harg : (↑(-t / τ : ℝ) : ℂ) + (-(Complex.I * (ω:ℂ) * (t:ℂ)))
        = t • (-( ((1/τ:ℝ):ℂ) + Complex.I * (ω:ℂ))) := by
    -- unfold smul
    simp [Algebra.smul_def, hτ]
    ring_nf
  -- now combine
  calc
    ((Real.exp (-t / τ) : ℝ) : ℂ) * Complex.exp (-(Complex.I * (ω:ℂ) * (t:ℂ)))
        = Complex.exp (↑(-t / τ : ℝ)) * Complex.exp (-(Complex.I * (ω:ℂ) * (t:ℂ))) := by
            simp [h1]
    _ = Complex.exp ((↑(-t / τ : ℝ) : ℂ) + (-(Complex.I * (ω:ℂ) * (t:ℂ)))) := by
            symm
            simpa using (Complex.exp_add (↑(-t/τ : ℝ) : ℂ) (-(Complex.I * (ω:ℂ) * (t:ℂ))))
    _ = Complex.exp (t • (-( ((1/τ:ℝ):ℂ) + Complex.I * (ω:ℂ)))) := by
            simp [harg]

end

end Scratch
