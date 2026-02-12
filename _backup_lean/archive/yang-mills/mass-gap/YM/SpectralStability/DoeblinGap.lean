import Mathlib

/-!
Doeblin-style contraction factor and "golden gap" positivity.

Setup:
  • Fix θ ∈ (0,1] and ρ : ℝ → ℝ with ρ(λ) ∈ (0,1) for λ > 0.
  • Define q(λ) := 1 − θ * ρ(λ).

Results:
  • q_in_unit_interval: ∀ λ > 0, 0 < q(λ) ∧ q(λ) < 1.
  • gap_pos_from_q: ∀ λ > 0, 0 < −Real.log (q(λ)).
-/

namespace YM.SpectralStability.DoeblinGap

open Real

/-- Assumptions for the Doeblin-style contraction setup. -/
structure Assumptions where
  θ : ℝ
  ρ : ℝ → ℝ
  θ_pos : 0 < θ
  θ_le_one : θ ≤ 1
  ρ_bounds : ∀ λ : ℝ, 0 < λ → (0 < ρ λ ∧ ρ λ < 1)

namespace Assumptions

variable (A : Assumptions)

/-- q(λ) := 1 − θ * ρ(λ). -/
def q (λ : ℝ) : ℝ := 1 - A.θ * A.ρ λ

/-- For every λ>0, 0 < q(λ) ∧ q(λ) < 1. -/
theorem q_in_unit_interval {λ : ℝ} (hλ : 0 < λ) :
    0 < A.q λ ∧ A.q λ < 1 := by
  have hρpos : 0 < A.ρ λ := (A.ρ_bounds λ hλ).left
  have hρlt1 : A.ρ λ < 1 := (A.ρ_bounds λ hλ).right
  -- 0 < θ * ρ(λ)
  have hpos_mul : 0 < A.θ * A.ρ λ := mul_pos A.θ_pos hρpos
  -- θ * ρ(λ) ≤ ρ(λ) < 1, hence θ * ρ(λ) < 1
  have hmul_le : A.θ * A.ρ λ ≤ 1 * A.ρ λ :=
    mul_le_mul_of_nonneg_right A.θ_le_one (le_of_lt hρpos)
  have hmul_lt_one : A.θ * A.ρ λ < 1 :=
    (lt_of_le_of_lt hmul_le (by simpa using hρlt1))
  -- 0 < 1 - θρ < 1
  have hleft : 0 < 1 - A.θ * A.ρ λ := sub_pos.mpr hmul_lt_one
  have hright : 1 - A.θ * A.ρ λ < 1 := sub_lt_self _ hpos_mul
  exact And.intro hleft hright

/-- For every λ>0, −log(q(λ)) > 0. -/
theorem gap_pos_from_q {λ : ℝ} (hλ : 0 < λ) :
    0 < -Real.log (A.q λ) := by
  have hI := A.q_in_unit_interval hλ
  have hq_pos : 0 < A.q λ := hI.left
  have hq_lt_one : A.q λ < 1 := hI.right
  -- log(q(λ)) < 0 since q(λ) < exp(0) and q(λ) > 0
  have hlog_neg : Real.log (A.q λ) < 0 := by
    -- log x < y ↔ x < exp y (for x > 0)
    have := (Real.log_lt_iff_lt_exp hq_pos).2
      (by simpa [Real.exp_zero] using hq_lt_one)
    simpa using this
  exact neg_pos.mpr hlog_neg

end Assumptions

end YM.SpectralStability.DoeblinGap

/-!
Public (parameterized) version matching the LaTeX interface:
  q θ ρ λ := 1 − θ * ρ λ
  q_in_unit_interval (θ, ρ)
  gap_pos_from_q       (θ, ρ)
-/

namespace YM.SpectralStability.DoeblinGap

namespace Public

def q (θ : ℝ) (ρ : ℝ → ℝ) (λ : ℝ) : ℝ := 1 - θ * ρ λ

theorem q_in_unit_interval
    (θ : ℝ) (ρ : ℝ → ℝ)
    (hθ_pos : 0 < θ) (hθ_le_one : θ ≤ 1)
    (hρ_bounds : ∀ λ : ℝ, 0 < λ → (0 < ρ λ ∧ ρ λ < 1))
    {λ : ℝ} (hλ : 0 < λ) :
    0 < q θ ρ λ ∧ q θ ρ λ < 1 := by
  -- Package in the `Assumptions` structure and reuse its theorem
  let A : Assumptions :=
    { θ := θ, ρ := ρ, θ_pos := hθ_pos, θ_le_one := hθ_le_one, ρ_bounds := hρ_bounds }
  simpa [q, Assumptions.q] using (A.q_in_unit_interval (λ:=λ) hλ)

theorem gap_pos_from_q
    (θ : ℝ) (ρ : ℝ → ℝ)
    (hθ_pos : 0 < θ) (hθ_le_one : θ ≤ 1)
    (hρ_bounds : ∀ λ : ℝ, 0 < λ → (0 < ρ λ ∧ ρ λ < 1))
    {λ : ℝ} (hλ : 0 < λ) :
    0 < -Real.log (q θ ρ λ) := by
  let A : Assumptions :=
    { θ := θ, ρ := ρ, θ_pos := hθ_pos, θ_le_one := hθ_le_one, ρ_bounds := hρ_bounds }
  simpa [q, Assumptions.q] using (A.gap_pos_from_q (λ:=λ) hλ)

end Public

end YM.SpectralStability.DoeblinGap
