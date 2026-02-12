import Mathlib
open scoped BigOperators

variable {Pos : Type} [Fintype Pos]

example (x : Pos → ℝ) (a : ℝ) : (∑ p : Pos, x p) * a = ∑ p : Pos, x p * a := by
  classical
  simpa using (Finset.sum_mul (s := (Finset.univ : Finset Pos)) (f := x) (a := a))
