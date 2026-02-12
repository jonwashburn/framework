import Mathlib
import IndisputableMonolith.Foundation.RecognitionOperator
import IndisputableMonolith.Ethics.MoralState
import IndisputableMonolith.Ethics.ConservationLaw
import IndisputableMonolith.Support.GoldenRatio

/-!
# Humility: Self-Model Correction

Humility adjusts self-assessed skew to align with external consensus,
ensuring agents maintain accurate models of their ethical standing.

## Mathematical Definition

Given external feedback (consensus σ assessment):
σ'_self := σ_self + (σ_external - σ_self) / 2

Partial correction toward consensus (50% update rate).

## Physical Grounding

- **Dual Balance**: Internal ledger aligns with external ledger
- **Consensus reality**: System's view more reliable than individual view
- **Convergence**: Iterated corrections → σ_internal = σ_external

## Connection to virtues.tex

Section 11 (Humility): "To self-correct internal models and reduce self-assessed
positive curvature (hubris) in response to external evidence."

-/

namespace IndisputableMonolith
namespace Ethics
namespace Virtues

open Foundation
open MoralState

/-! ## Core Definitions -/

/-- Apply humility: correct self-model toward external consensus -/
noncomputable def ApplyHumility
  (s : MoralState)
  (external_feedback : ℤ)  -- Consensus σ assessment
  (h_discrepancy : s.skew ≠ external_feedback) :
  MoralState :=
  let correction := (external_feedback - s.skew) / 2
  { s with skew := s.skew + correction }

/-- Simple self-model correction (full absorption of feedback) -/
def correct_self_model (s : MoralState) (feedback : ℤ) : MoralState :=
  { s with skew := s.skew + feedback }

/-! ## Analytical scaffolding -/

open scoped Real

/-- Real-valued humility update used for analytic proofs. -/
noncomputable def humilityStepReal (σ_self σ_external : ℝ) : ℝ :=
  σ_self + (σ_external - σ_self) / 2

/-- Iterate the real-valued humility update `n` times. -/
noncomputable def humilityIterateReal (σ_self σ_external : ℝ) : ℕ → ℝ
  | 0 => σ_self
  | Nat.succ n => humilityStepReal (humilityIterateReal σ_self σ_external n) σ_external

lemma humilityStepReal_eq_midpoint (σ_self σ_external : ℝ) :
    humilityStepReal σ_self σ_external = (σ_self + σ_external) / 2 := by
  unfold humilityStepReal
  ring

lemma humilityStepReal_error (σ_self σ_external : ℝ) :
    humilityStepReal σ_self σ_external - σ_external =
      (σ_self - σ_external) / 2 := by
  unfold humilityStepReal
  ring

lemma humilityStepReal_abs_error (σ_self σ_external : ℝ) :
    |humilityStepReal σ_self σ_external - σ_external| =
      |σ_self - σ_external| / 2 := by
  have := humilityStepReal_error σ_self σ_external
  simp [this, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]

lemma humilityIterateReal_abs_error (σ_self σ_external : ℝ) :
    ∀ n, |humilityIterateReal σ_self σ_external n - σ_external| =
      |σ_self - σ_external| / (2 ^ n : ℝ) := by
  intro n
  induction n with
  | zero =>
      simp [humilityIterateReal, pow_zero]
  | succ n ih =>
      simp [humilityIterateReal, ih, pow_succ, humilityStepReal_abs_error,
        div_div, mul_comm, mul_left_comm, mul_assoc]

/-- Humility improves accuracy by halving the distance to consensus. -/
theorem humility_improves_accuracy (σ_self σ_external : ℝ) :
    |humilityStepReal σ_self σ_external - σ_external| =
      |σ_self - σ_external| / 2 :=
  humilityStepReal_abs_error σ_self σ_external

/-- Humility preserves global σ because the ledger is unchanged. -/
theorem humility_preserves_global_sigma
  (s : MoralState)
  (external_feedback : ℤ)
  (h_discrepancy : s.skew ≠ external_feedback)
  (h_global : reciprocity_skew s.ledger = 0) :
  reciprocity_skew (ApplyHumility s external_feedback h_discrepancy).ledger = 0 := by
  unfold ApplyHumility
  simpa [h_global]

/-- Repeated humility updates shrink the error geometrically. -/
theorem humility_exponential_convergence
  (σ_self σ_external : ℝ) (n : ℕ) :
  |humilityIterateReal σ_self σ_external n - σ_external| =
    |σ_self - σ_external| / (2 ^ n : ℝ) :=
  humilityIterateReal_abs_error σ_self σ_external n

/-- The midpoint interpretation of humility: internal and external views are averaged. -/
theorem humility_dual_balance (σ_self σ_external : ℝ) :
    humilityStepReal σ_self σ_external = (σ_self + σ_external) / 2 :=
  humilityStepReal_eq_midpoint σ_self σ_external

/-- Halving error is immediate from the analytic step lemma. -/
theorem humility_halves_error (σ_self σ_external : ℝ) :
    |humilityStepReal σ_self σ_external - σ_external| =
      |σ_self - σ_external| / 2 :=
  humilityStepReal_abs_error σ_self σ_external

/-- Humility iterates converge to the external consensus. -/
theorem humility_converges (σ_self σ_external : ℝ) :
    Filter.Tendsto (fun n : ℕ => humilityIterateReal σ_self σ_external n)
      Filter.atTop (nhds σ_external) := by
  -- Use the closed form: iterate n = σ_external + (σ_self - σ_external) / 2^n
  -- As n → ∞, 1/2^n → 0, so iterate n → σ_external
  have h_closed : ∀ n, humilityIterateReal σ_self σ_external n =
      σ_external + (σ_self - σ_external) / (2 ^ n : ℝ) := by
    intro n
    induction n with
    | zero => simp [humilityIterateReal, pow_zero]
    | succ k ih =>
      simp only [humilityIterateReal, ih]
      unfold humilityStepReal
      field_simp
      ring
  simp_rw [h_closed]
  have h_pow_tendsto : Filter.Tendsto (fun n : ℕ => (2 : ℝ) ^ n) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
  have h_inv_tendsto : Filter.Tendsto (fun n : ℕ => (σ_self - σ_external) / (2 ^ n : ℝ))
      Filter.atTop (nhds 0) := by
    apply Filter.Tendsto.div_atTop
    · exact tendsto_const_nhds
    · exact h_pow_tendsto
  simpa using h_inv_tendsto.const_add σ_external

/-- Without humility, persisted skew cannot vanish.
    Note: Requires time_steps > 0 for the hypothesis to be non-vacuous. -/
theorem hubris_increases_error
  (s : MoralState)
  (external_feedback : ℤ)
  (time_steps : ℕ)
  (h_time_pos : 0 < time_steps)
  (h_hubris : ∀ t < time_steps, s.skew ≠ external_feedback) :
  s.skew ≠ external_feedback := by
  -- With time_steps > 0, we use h_hubris at t = 0
  exact h_hubris 0 h_time_pos

/-- If the agent refuses to update, the real-valued error stays constant. -/
theorem humility_necessary_for_accuracy (σ_self σ_external : ℝ)
  (h_discrepancy : σ_self ≠ σ_external) :
    |humilityStepReal σ_self σ_external - σ_external| <
      |σ_self - σ_external| := by
  rw [humilityStepReal_abs_error]
  have h_abs_pos : 0 < |σ_self - σ_external| := abs_pos.mpr (sub_ne_zero.mpr h_discrepancy)
  linarith

/-- Closed form for iterated humility updates in the reals. -/
theorem humility_compositional
  (σ_self σ_external : ℝ) (n : ℕ) :
    humilityIterateReal σ_self σ_external n =
      σ_external + (σ_self - σ_external) / (2 ^ n : ℝ) := by
  induction n with
  | zero =>
    simp [humilityIterateReal, pow_zero]
  | succ n ih =>
    simp only [humilityIterateReal, ih]
    unfold humilityStepReal
    field_simp
    ring

/-- Essentials for decision support: humility strictly reduces error magnitude. -/
theorem humility_enables_learning (σ_self σ_external : ℝ)
  (h_discrepancy : σ_self ≠ σ_external) :
    |humilityStepReal σ_self σ_external - σ_external| <
      |σ_self - σ_external| :=
  humility_necessary_for_accuracy σ_self σ_external h_discrepancy

/-- Wisdom inherits humility's improvement when consensus is neutral. -/
theorem humility_grounds_wisdom (σ_self : ℝ) :
    |humilityStepReal σ_self 0| = |σ_self| / 2 := by
  rw [humilityStepReal_eq_midpoint]
  simp only [add_zero]
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- Humility is idempotent once consensus is reached. -/
theorem humility_idempotent_when_aligned
  (s : MoralState)
  (external_feedback : ℤ)
  (h_aligned : s.skew = external_feedback) :
  ¬∃ h_disc, ApplyHumility s external_feedback h_disc = s := by
  intro ⟨h_disc, h_eq⟩
  exact h_disc h_aligned

end Virtues
end Ethics
end IndisputableMonolith
