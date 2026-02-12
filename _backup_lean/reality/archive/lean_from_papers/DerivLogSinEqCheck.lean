import Mathlib

open Real

#check deriv (fun x : ℝ => Real.log (Real.sin x))
#check fun x : ℝ => Real.cot x

-- Check if simp can prove the global identity.
example : (deriv (fun x : ℝ => Real.log (Real.sin x))) = fun x : ℝ => Real.cot x := by
  funext x
  -- try simp?
  simp
