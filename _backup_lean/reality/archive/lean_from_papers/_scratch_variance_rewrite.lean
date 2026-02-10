import Mathlib
open scoped BigOperators

variable {Pos : Type} [Fintype Pos]

example (x : Pos → ℝ) (μ : ℝ) :
    (∑ p : Pos, (x p ^ 2 - 2 * μ * x p + μ ^ 2)) =
      (∑ p : Pos, x p ^ 2) - (∑ p : Pos, 2 * μ * x p) + (Fintype.card Pos : ℝ) * μ ^ 2 := by
  classical
  -- split as (x^2 - 2μx) + μ^2
  have : (∑ p : Pos, (x p ^ 2 - 2 * μ * x p + μ ^ 2)) =
      (∑ p : Pos, (x p ^ 2 - 2 * μ * x p)) + (∑ _p : Pos, μ ^ 2) := by
    -- rewrite each summand and use sum_add_distrib
    simp [add_assoc, Finset.sum_add_distrib]
  -- now rewrite first sum using sum_sub_distrib and simplify const sum
  --
  --
  --
  --
  --
  
  -- Continue from `this`
  rw [this]
  -- sum_sub_distrib
  --
  
  -- simplify both pieces
  -- `simp` should turn ∑ p, (x p ^2 - 2μx p) into (∑ x^2) - (∑ 2μx)
  -- and ∑ _p, μ^2 into card * μ^2
  
  simp [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, add_assoc, add_left_comm, add_comm, sub_eq_add_neg]
