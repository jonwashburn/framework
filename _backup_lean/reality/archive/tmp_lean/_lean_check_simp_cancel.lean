import Mathlib

open Complex

example (a : ℂ) (ha : a ≠ 0) : (-a) * (-a)⁻¹ = (1:ℂ) := by
  simp [ha]
