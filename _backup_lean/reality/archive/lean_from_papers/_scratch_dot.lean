import Mathlib

#check norm_ofReal
#check Complex.norm_ofReal

example (x : ℝ) : ‖(x : ℂ)‖ = |x| := by
  -- this works via dot-notation (sets the ambient `IsROrC` type to ℂ)
  simpa using (Complex.norm_ofReal x)
