import Mathlib
open scoped BigOperators

variable {Pos : Type} [Fintype Pos]

example (x : Pos → ℝ) (μ : ℝ) :
    (∑ p : Pos, (x p ^ 2 - 2 * μ * x p + μ ^ 2)) =
      (∑ p : Pos, x p ^ 2) - (∑ p : Pos, 2 * μ * x p) + (Fintype.card Pos : ℝ) * μ ^ 2 := by
  classical
  have h1 : (∑ p : Pos, (x p ^ 2 - 2 * μ * x p + μ ^ 2)) =
      (∑ p : Pos, (x p ^ 2 - 2 * μ * x p)) + (∑ _p : Pos, μ ^ 2) := by
    simp [Finset.sum_add_distrib, add_assoc]
  rw [h1]
  simp [sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, add_assoc, add_left_comm, add_comm]
