import Mathlib

open scoped BigOperators

example (v0 : Fin 8 → ℂ) :
    (∑ x : Fin 8, (starRingEnd ℂ) (v0 x) * v0 x) = (∑ x : Fin 8, star (v0 x) * v0 x) := by
  simp
