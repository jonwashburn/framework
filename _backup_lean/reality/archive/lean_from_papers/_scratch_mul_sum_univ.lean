import Mathlib
open scoped BigOperators

variable {Pos : Type} [Fintype Pos]

example (x : Pos → ℝ) (μ : ℝ) : (∑ p : Pos, (2*μ) * x p) = (2*μ) * (∑ p : Pos, x p) := by
  classical
  simpa using (Finset.mul_sum (s := (Finset.univ : Finset Pos)) (f := x) (a := (2*μ))).symm
