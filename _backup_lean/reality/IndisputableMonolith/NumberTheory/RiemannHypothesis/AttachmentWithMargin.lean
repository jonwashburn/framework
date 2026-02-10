import IndisputableMonolith.NumberTheory.RiemannHypothesis.BRFPlumbing

/-!
# RH (Christmas route): quantitative attachment with margin

`Riemann-Christmas.tex` isolates the far-field remaining gap as the **attachment-with-margin**
inequality (equation `eq:attachment`):

`sup_{s ∈ R} |J_N(s) - J_cert,N(s)| ≤ m_R / 4`, where `m_R := inf_{s ∈ R} Re(2 J_cert,N(s))`.

This file formalizes the *purely algebraic* consequence:

`(attachment-with-margin) ⇒ Re(2 J_N) ≥ 0` (hence the Cayley transform is Schur),

without touching any number theory. The analytic difficulty is entirely in proving the
uniform approximation bound itself.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace RiemannHypothesis

open scoped Real

/-!
## One-step algebra: approximation within margin ⇒ Herglotz/Schur on a set
-/

/-- The **Christmas-route attachment-with-margin** predicate on a set `R`.

This is the one-line analytic gap from `Riemann-Christmas.tex` (`eq:attachment`), expressed
pointwise (which is implied by the `sup` version).
-/
def AttachmentWithMargin (R : Set ℂ) (J Jcert : ℂ → ℂ) (m : ℝ) : Prop :=
  0 ≤ m ∧ (∀ s ∈ R, m ≤ (2 * Jcert s).re) ∧ (∀ s ∈ R, ‖J s - Jcert s‖ ≤ m / 4)

/-- A convenient “budget form”: it suffices to bound the uniform approximation error by a
sum of nonnegative budgets `Etail + Ewin` and then check `Etail + Ewin ≤ m/4`. -/
theorem attachmentWithMargin_of_errorBudget
    {R : Set ℂ} {J Jcert : ℂ → ℂ} {m Etail Ewin : ℝ}
    (hm_nonneg : 0 ≤ m)
    (hmargin : ∀ s ∈ R, m ≤ (2 * Jcert s).re)
    (herr : ∀ s ∈ R, ‖J s - Jcert s‖ ≤ Etail + Ewin)
    (hbudget : Etail + Ewin ≤ m / 4) :
    AttachmentWithMargin R J Jcert m := by
  refine ⟨hm_nonneg, hmargin, ?_⟩
  intro s hs
  exact (herr s hs).trans hbudget

/-- **Quantitative attachment with margin** (algebraic core).

Let `Jcert` be a "certificate" function and `J` an approximant. If, on a set `R`,

- `Re(2*Jcert)` is bounded below by a nonnegative margin `m`, and
- `J` stays within `m/4` (in norm) of `Jcert`,

then `Re(2*J) ≥ 0` on `R`.

This is the Lean analogue of `Riemann-Christmas.tex`, Lemma `attachment-identity`
(the step after equation `eq:attachment` is assumed).
-/
theorem re_two_mul_nonneg_of_attachmentWithMargin
    {R : Set ℂ} {J Jcert : ℂ → ℂ} {m : ℝ}
    (hm_nonneg : 0 ≤ m)
    (hmargin : ∀ s ∈ R, m ≤ (2 * Jcert s).re)
    (hclose : ∀ s ∈ R, ‖J s - Jcert s‖ ≤ m / 4) :
    ∀ s ∈ R, 0 ≤ (2 * J s).re := by
  intro s hs
  have hJcert : m ≤ (2 * Jcert s).re := hmargin s hs
  have hdiff : ‖J s - Jcert s‖ ≤ m / 4 := hclose s hs

  -- Control the real part of the perturbation by its norm.
  have hAbsRe :
      |(2 * (J s - Jcert s)).re| ≤ ‖2 * (J s - Jcert s)‖ :=
    Complex.abs_re_le_norm _
  have hRe_lower :
      -‖2 * (J s - Jcert s)‖ ≤ (2 * (J s - Jcert s)).re :=
    (abs_le.mp hAbsRe).1

  -- Convert `‖2 * (J-Jcert)‖` into `2 * ‖J-Jcert‖` and use the `m/4` bound.
  have hnorm_two : ‖(2 : ℂ)‖ = (2 : ℝ) := by
    -- `‖(x:ℂ)‖ = |x|` for real `x`, and `|2|=2`.
    simp
  have hnorm_mul :
      ‖2 * (J s - Jcert s)‖ ≤ m / 2 := by
    -- `‖2 * z‖ = ‖2‖ * ‖z‖ = 2 * ‖z‖`.
    have hnorm :
        ‖2 * (J s - Jcert s)‖ = (2 : ℝ) * ‖J s - Jcert s‖ := by
      simpa [mul_assoc, hnorm_two] using
        (norm_mul (2 : ℂ) (J s - Jcert s))
    -- Multiply the `m/4` bound by `2`.
    have hmul : (2 : ℝ) * ‖J s - Jcert s‖ ≤ (2 : ℝ) * (m / 4) :=
      mul_le_mul_of_nonneg_left hdiff (by norm_num : (0 : ℝ) ≤ 2)
    -- `2 * (m/4) = m/2`
    have hmul_simp : (2 : ℝ) * (m / 4) = m / 2 := by ring
    -- Finish.
    -- Rewrite the left-hand side using `hnorm`, then close by `hmul` and `hmul_simp`.
    calc
      ‖2 * (J s - Jcert s)‖ = (2 : ℝ) * ‖J s - Jcert s‖ := hnorm
      _ ≤ (2 : ℝ) * (m / 4) := hmul
      _ = m / 2 := hmul_simp

  -- Now bound the target real part:
  --   Re(2J) = Re(2Jcert) + Re(2(J-Jcert)) ≥ m - ‖2(J-Jcert)‖ ≥ m/2 ≥ 0.
  have hRe2 :
      (2 * J s).re ≥ m - ‖2 * (J s - Jcert s)‖ := by
    -- `2*J = 2*Jcert + 2*(J-Jcert)`
    have hsplit : (2 * J s) = (2 * Jcert s) + (2 * (J s - Jcert s)) := by
      ring
    -- Take real parts and use the perturbation lower bound.
    -- `re(a+b) = re(a) + re(b)`
    have : (2 * J s).re = (2 * Jcert s).re + (2 * (J s - Jcert s)).re := by
      simpa [hsplit, Complex.add_re]
    -- combine
    nlinarith [this, hJcert, hRe_lower]

  have : (2 * J s).re ≥ m / 2 := by
    nlinarith [hRe2, hnorm_mul]
  have : 0 ≤ (2 * J s).re := by
    nlinarith [this, hm_nonneg]
  simpa using this

/-- Wrapper: `AttachmentWithMargin` implies `Re(2*J) ≥ 0` on `R`. -/
theorem re_two_mul_nonneg_of_AttachmentWithMargin
    {R : Set ℂ} {J Jcert : ℂ → ℂ} {m : ℝ}
    (h : AttachmentWithMargin R J Jcert m) :
    ∀ s ∈ R, 0 ≤ (2 * J s).re := by
  rcases h with ⟨hm_nonneg, hmargin, hclose⟩
  exact re_two_mul_nonneg_of_attachmentWithMargin
    (R := R) (J := J) (Jcert := Jcert) (m := m) hm_nonneg hmargin hclose

/-- Attachment-with-margin also yields the Schur (disk) bound for the Cayley transform `theta`. -/
theorem norm_theta_le_one_of_attachmentWithMargin
    {R : Set ℂ} {J Jcert : ℂ → ℂ} {m : ℝ}
    (hm_nonneg : 0 ≤ m)
    (hmargin : ∀ s ∈ R, m ≤ (2 * Jcert s).re)
    (hclose : ∀ s ∈ R, ‖J s - Jcert s‖ ≤ m / 4) :
    ∀ s ∈ R, ‖theta (J s)‖ ≤ 1 := by
  intro s hs
  have hRe : 0 ≤ (2 * J s).re :=
    re_two_mul_nonneg_of_attachmentWithMargin (R := R) (J := J) (Jcert := Jcert)
      (m := m) hm_nonneg hmargin hclose s hs
  -- Cayley: if `Re(2J) ≥ 0` then `‖cayley(2J)‖ ≤ 1`, i.e. `‖theta J‖ ≤ 1`.
  simpa [theta] using (norm_cayley_le_one_of_re_nonneg (z := 2 * J s) hRe)

/-- Wrapper: `AttachmentWithMargin` implies the Schur bound `‖theta (J s)‖ ≤ 1` on `R`. -/
theorem norm_theta_le_one_of_AttachmentWithMargin
    {R : Set ℂ} {J Jcert : ℂ → ℂ} {m : ℝ}
    (h : AttachmentWithMargin R J Jcert m) :
    ∀ s ∈ R, ‖theta (J s)‖ ≤ 1 := by
  rcases h with ⟨hm_nonneg, hmargin, hclose⟩
  exact norm_theta_le_one_of_attachmentWithMargin
    (R := R) (J := J) (Jcert := Jcert) (m := m) hm_nonneg hmargin hclose

end RiemannHypothesis
end NumberTheory
end IndisputableMonolith
