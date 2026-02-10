import Mathlib

example (S : ℂ) : ‖S / (Real.sqrt 8 : ℂ)‖ = ‖S‖ / ‖(Real.sqrt 8 : ℂ)‖ := by
  simpa using (norm_div S (Real.sqrt 8 : ℂ))

example (S : ℂ) : True := by
  have _h := (norm_div S (Real.sqrt 8 : ℂ))
  trivial
