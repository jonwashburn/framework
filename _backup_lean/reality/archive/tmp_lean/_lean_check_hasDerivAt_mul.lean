import Mathlib

#check (by
  have : HasDerivAt (fun t : ℝ => (2:ℂ) * t) (2:ℂ) 0 := by
    simpa using (hasDerivAt_const_mul (c := (2:ℂ)) (x := (fun t : ℝ => t)) (x0 := 0))
  exact this)
