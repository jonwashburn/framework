import Mathlib

#check Complex.normSq
#check Complex.normSq_ofReal
#check Complex.normSq_neg

example (r : ℝ) : Complex.normSq (r : ℂ) = r^2 := by
  -- `Complex.normSq_ofReal r : Complex.normSq (r:ℂ) = r*r`
  simpa [pow_two] using (Complex.normSq_ofReal r)
