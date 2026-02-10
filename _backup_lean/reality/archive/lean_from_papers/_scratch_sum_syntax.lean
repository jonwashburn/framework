import Mathlib
open scoped BigOperators

example (s : Finset Nat) (f : Nat → Nat) : (∑ x in s, f x) = (∑ x in s, f x) := by
  rfl
