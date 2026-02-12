import Mathlib

example (z w : ℂ) : ‖z / w‖ = ‖z‖ / ‖w‖ := by
  simpa using (Complex.norm_div z w)

example : ‖((1:ℂ) / (2:ℂ))‖ = ‖(1:ℂ)‖ / ‖(2:ℂ)‖ := by
  simpa using (Complex.norm_div (1:ℂ) (2:ℂ))
