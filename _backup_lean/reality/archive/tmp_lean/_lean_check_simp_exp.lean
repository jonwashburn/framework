import Mathlib

open Complex
open scoped Real

example (t τ : ℝ) : (↑(Real.exp (-t / τ)) : ℂ) = Complex.exp (-( (t:ℂ) * ((1/τ:ℝ):ℂ))) := by
  -- just see if simp can do it
  -- (-t/τ) = -(t*(1/τ))
  have : (-t / τ : ℝ) = -(t * (1/τ)) := by
    ring
  -- convert via ofReal_exp
  -- might need coercions
  simp [Complex.ofReal_exp, this, mul_assoc, mul_comm, mul_left_comm]
