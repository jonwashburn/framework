import Mathlib
open scoped BigOperators

variable {Pos : Type} [Fintype Pos]

theorem mean_variance_le_total_scratch (x : Pos → ℝ) :
    let μ := (∑ p : Pos, x p) / Fintype.card Pos
    ∑ p : Pos, (x p - μ) ^ 2 ≤ ∑ p : Pos, x p ^ 2 := by
  classical
  intro μ
  have h_expand : ∀ p, (x p - μ) ^ 2 = x p ^ 2 - 2 * μ * x p + μ ^ 2 := fun p => by ring
  simp_rw [h_expand]
  -- rewrite the LHS sum
  have hdecomp : (∑ p : Pos, (x p ^ 2 - 2 * μ * x p + μ ^ 2)) =
      (∑ p : Pos, x p ^ 2) - (∑ p : Pos, 2 * μ * x p) + (Fintype.card Pos : ℝ) * μ ^ 2 := by
    have h1 : (∑ p : Pos, (x p ^ 2 - 2 * μ * x p + μ ^ 2)) =
        (∑ p : Pos, (x p ^ 2 - 2 * μ * x p)) + (∑ _p : Pos, μ ^ 2) := by
      simp [Finset.sum_add_distrib]
    rw [h1]
    -- first sum
    simp [sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    -- constant sum
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, add_assoc, add_comm, add_left_comm]
  rw [hdecomp]

  have hsum_mul : (∑ p : Pos, 2 * μ * x p) = 2 * μ * (∑ p : Pos, x p) := by
    -- factor constant on the left
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (Finset.mul_sum (s := (Finset.univ : Finset Pos)) (f := x) (a := (2 * μ))).symm

  have h_sum_eq : 2 * μ * (∑ p : Pos, x p) = 2 * (Fintype.card Pos : ℝ) * μ ^ 2 := by
    simp only [μ]
    by_cases h_card : (Fintype.card Pos : ℝ) = 0
    · simp [h_card]
    · field_simp [h_card]
      ring

  -- use the identities to reduce to A - nμ² ≤ A
  have hnonneg : 0 ≤ (Fintype.card Pos : ℝ) * μ ^ 2 := by
    have hcard : 0 ≤ (Fintype.card Pos : ℝ) := by exact_mod_cast Nat.cast_nonneg (Fintype.card Pos)
    exact mul_nonneg hcard (sq_nonneg μ)

  -- rewrite the middle term and finish
  --
  -- LHS = A - (2μ∑x) + nμ² = A - (2nμ²) + nμ² = A - nμ²
  --
  have hA :
      (∑ p : Pos, x p ^ 2) - (∑ p : Pos, 2 * μ * x p) + (Fintype.card Pos : ℝ) * μ ^ 2
        = (∑ p : Pos, x p ^ 2) - (Fintype.card Pos : ℝ) * μ ^ 2 := by
    -- substitute ∑ 2μx = 2μ∑x = 2nμ²
    rw [hsum_mul]
    -- cancel 2 from h_sum_eq
    have h_cancel : μ * (∑ p : Pos, x p) = (Fintype.card Pos : ℝ) * μ ^ 2 := by
      have h2 : (2 : ℝ) ≠ 0 := by norm_num
      -- from 2*(μ*Σx)=2*(n*μ²)
      have : (2 : ℝ) * (μ * (∑ p : Pos, x p)) = (2 : ℝ) * ((Fintype.card Pos : ℝ) * μ ^ 2) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using h_sum_eq
      exact (mul_left_cancel₀ h2 this)
    -- now simplify
    -- replace 2*μ*Σx with 2*(nμ²)
    have : (2 : ℝ) * μ * (∑ p : Pos, x p) = (2 : ℝ) * ((Fintype.card Pos : ℝ) * μ ^ 2) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using congrArg (fun t => (2 : ℝ) * t) h_cancel
    -- ring the expression
    nlinarith [this]

  -- finish using sub_le_self
  have : (∑ p : Pos, x p ^ 2) - (Fintype.card Pos : ℝ) * μ ^ 2 ≤ ∑ p : Pos, x p ^ 2 :=
    sub_le_self _ hnonneg
  simpa [hA] using this
