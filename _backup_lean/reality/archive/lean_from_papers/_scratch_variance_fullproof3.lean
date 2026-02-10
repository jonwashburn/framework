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

  have hdecomp : (∑ p : Pos, (x p ^ 2 - 2 * μ * x p + μ ^ 2)) =
      (∑ p : Pos, x p ^ 2) - (∑ p : Pos, 2 * μ * x p) + (Fintype.card Pos : ℝ) * μ ^ 2 := by
    have h1 : (∑ p : Pos, (x p ^ 2 - 2 * μ * x p + μ ^ 2)) =
        (∑ p : Pos, (x p ^ 2 - 2 * μ * x p)) + (∑ _p : Pos, μ ^ 2) := by
      simp [Finset.sum_add_distrib]
    rw [h1]
    simp [sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

  rw [hdecomp]

  have hsum_mul : (∑ p : Pos, 2 * μ * x p) = 2 * μ * (∑ p : Pos, x p) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (Finset.mul_sum (s := (Finset.univ : Finset Pos)) (f := x) (a := (2 * μ))).symm

  have h_sum_eq : 2 * μ * (∑ p : Pos, x p) = 2 * (Fintype.card Pos : ℝ) * μ ^ 2 := by
    simp only [μ]
    by_cases h_card : (Fintype.card Pos : ℝ) = 0
    · simp [h_card]
    · field_simp [h_card]

  have hsum_eq' : (∑ p : Pos, 2 * μ * x p) = 2 * (Fintype.card Pos : ℝ) * μ ^ 2 := by
    calc
      (∑ p : Pos, 2 * μ * x p) = 2 * μ * (∑ p : Pos, x p) := hsum_mul
      _ = 2 * (Fintype.card Pos : ℝ) * μ ^ 2 := h_sum_eq

  rw [hsum_eq']

  have hnonneg : 0 ≤ (Fintype.card Pos : ℝ) * μ ^ 2 := by
    have hcard : 0 ≤ (Fintype.card Pos : ℝ) := by exact_mod_cast Nat.cast_nonneg (Fintype.card Pos)
    exact mul_nonneg hcard (sq_nonneg μ)

  have hrew :
      (∑ p : Pos, x p ^ 2) - (2 * (Fintype.card Pos : ℝ) * μ ^ 2) + (Fintype.card Pos : ℝ) * μ ^ 2
        = (∑ p : Pos, x p ^ 2) - (Fintype.card Pos : ℝ) * μ ^ 2 := by
    ring

  simpa [hrew] using (sub_le_self (∑ p : Pos, x p ^ 2) hnonneg)
