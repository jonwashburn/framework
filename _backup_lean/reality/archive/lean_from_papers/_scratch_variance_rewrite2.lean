import Mathlib
open scoped BigOperators

variable {Pos : Type} [Fintype Pos]

example (x : Pos → ℝ) (μ : ℝ) :
    (∑ p : Pos, (x p ^ 2 - 2 * μ * x p)) = (∑ p : Pos, x p ^ 2) - (∑ p : Pos, 2 * μ * x p) := by
  classical
  -- rewrite subtraction as addition of neg
  simp [sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]

example (x : Pos → ℝ) (μ : ℝ) :
    (∑ p : Pos, (x p ^ 2 - 2 * μ * x p + μ ^ 2)) =
      (∑ p : Pos, x p ^ 2) - (∑ p : Pos, 2 * μ * x p) + (Fintype.card Pos : ℝ) * μ ^ 2 := by
  classical
  -- split last + μ^2
  have h1 : (∑ p : Pos, (x p ^ 2 - 2 * μ * x p + μ ^ 2)) =
      (∑ p : Pos, (x p ^ 2 - 2 * μ * x p)) + (∑ _p : Pos, μ ^ 2) := by
    simp [add_assoc, Finset.sum_add_distrib]
  rw [h1]
  -- rewrite first sum as (∑ x^2) - (∑ 2μx)
  simp [Finset.sum_neg_distrib, sub_eq_add_neg, Finset.sum_add_distrib]
  -- rewrite the constant sum
  simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
