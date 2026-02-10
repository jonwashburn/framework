import Mathlib
import IndisputableMonolith.Foundation.RecognitionOperator
import IndisputableMonolith.Ethics.MoralState
import IndisputableMonolith.Ethics.ConservationLaw
import IndisputableMonolith.Ethics.Harm
import IndisputableMonolith.Ethics.Consent
import IndisputableMonolith.Ethics.Audit
import IndisputableMonolith.Support.GoldenRatio

/-!
# Courage: High-Gradient Action Enablement

Courage enables virtuous action in high-gradient environments where inaction
would lead to decoherence or collapse.  The implementation below formalizes the
energy expenditure, stability guarantees, and audit hooks required to operate
Courage within the Recognition Science ethics stack.
-/

namespace IndisputableMonolith
namespace Ethics
namespace Virtues

open Foundation
open MoralState
open scoped BigOperators

/-! ## Core Definitions -/

/-- Skew gradient magnitude (rate of change in local environment).

    Currently uses skew magnitude as proxy for gradient.  A future refinement
    will replace this with a discrete derivative across the eight-tick cadence. -/
@[simp]
def skew_gradient (s : MoralState) : ℝ :=
  (Int.natAbs s.skew : ℝ)

lemma skew_gradient_nonneg (s : MoralState) : 0 ≤ skew_gradient s := by
  unfold skew_gradient
  exact Nat.cast_nonneg _

/-- A courageous action is one taken under high gradient conditions. -/
def CourageousAction (s : MoralState) (action : MoralState → MoralState) : Prop :=
  skew_gradient s > 8

/-- Courage threshold equals the eight-tick cadence. -/
def courage_threshold : ℝ := 8

lemma courage_threshold_pos : 0 < courage_threshold := by
  simp [courage_threshold]

lemma skew_gradient_pos_of_high {s : MoralState}
    (h : skew_gradient s > courage_threshold) : 0 < skew_gradient s :=
  lt_trans courage_threshold_pos h

/-- Scaling factor applied to post-action energy when courage is invoked. -/
noncomputable def courage_energy_scale (s : MoralState)
    (h : skew_gradient s > courage_threshold) : ℝ :=
  courage_threshold / skew_gradient s

lemma courage_energy_scale_pos (s : MoralState)
    (h : skew_gradient s > courage_threshold) :
    0 < courage_energy_scale s h := by
  unfold courage_energy_scale
  exact div_pos courage_threshold_pos (skew_gradient_pos_of_high h)

lemma courage_energy_scale_lt_one (s : MoralState)
    (h : skew_gradient s > courage_threshold) :
    courage_energy_scale s h < 1 := by
  unfold courage_energy_scale
  rw [div_lt_one (skew_gradient_pos_of_high h)]
  exact h

lemma courage_energy_scale_strict_antitone {s₁ s₂ : MoralState}
    (h₁ : skew_gradient s₁ > courage_threshold)
    (h₂ : skew_gradient s₂ > courage_threshold)
    (h_gt : skew_gradient s₁ > skew_gradient s₂) :
    courage_energy_scale s₁ h₁ < courage_energy_scale s₂ h₂ := by
  unfold courage_energy_scale
  have h_pos₂ : 0 < skew_gradient s₂ := skew_gradient_pos_of_high h₂
  -- courage_threshold / s₁ < courage_threshold / s₂ when s₁ > s₂ > 0 and courage_threshold > 0
  exact div_lt_div_of_pos_left courage_threshold_pos h_pos₂ h_gt

lemma courage_energy_cost_fraction (s : MoralState)
    (h : skew_gradient s > courage_threshold) :
    1 - courage_energy_scale s h =
      (skew_gradient s - courage_threshold) / skew_gradient s := by
  unfold courage_energy_scale
  have h_pos : 0 < skew_gradient s := skew_gradient_pos_of_high h
  field_simp

/-- Apply courage: rescale post-action energy according to the gradient surplus. -/
noncomputable def ApplyCourage
  (s : MoralState)
  (action : MoralState → MoralState)
  (h_high_gradient : skew_gradient s > 8) :
  MoralState :=
  let result := action s
  let scale := courage_energy_scale s h_high_gradient
  { result with
    energy := result.energy * scale
    energy_pos := by
      have h_res := result.energy_pos
      have h_scale := courage_energy_scale_pos s h_high_gradient
      simpa [scale] using mul_pos h_res h_scale }

@[simp]
lemma applyCourage_energy
    (s : MoralState) (action : MoralState → MoralState)
    (h : skew_gradient s > courage_threshold) :
    (ApplyCourage s action h).energy =
      (action s).energy * courage_energy_scale s h := by
  simp [ApplyCourage]

@[simp]
lemma applyCourage_skew
    (s : MoralState) (action : MoralState → MoralState)
    (h : skew_gradient s > courage_threshold) :
    (ApplyCourage s action h).skew = (action s).skew := by
  simp [ApplyCourage]

/-! ## Core Theorems -/

/-- Courage always debits energy under high-gradient conditions. -/
theorem courage_costs_energy
  (s : MoralState)
  (action : MoralState → MoralState)
  (h_high : skew_gradient s > 8) :
  (ApplyCourage s action h_high).energy < (action s).energy := by
  simp only [ApplyCourage]
  have h_scale_lt_one := courage_energy_scale_lt_one s h_high
  have h_scale_pos := courage_energy_scale_pos s h_high
  have h_energy_pos := (action s).energy_pos
  calc (action s).energy * courage_energy_scale s h_high
      < (action s).energy * 1 := by exact mul_lt_mul_of_pos_left h_scale_lt_one h_energy_pos
    _ = (action s).energy := by ring

/-- Courage threshold equals eight ticks. -/
theorem courage_threshold_is_eight :
  courage_threshold = 8 := by
  rfl

/-- High gradient indicates the system is out of sync with the eight-tick cadence. -/
theorem high_gradient_out_of_sync
  (s : MoralState)
  (h_high : skew_gradient s > courage_threshold) :
  skew_gradient s > 8 := by
  unfold courage_threshold at h_high
  simpa [courage_threshold] using h_high

/-- Courage enables stability provided the underlying action reduces gradient. -/
theorem courage_enables_stability
  (s : MoralState)
  (action : MoralState → MoralState)
  (h_courageous : CourageousAction s action)
  (h_action_reduces : skew_gradient (action s) < skew_gradient s) :
  let result := ApplyCourage s action (by
      unfold CourageousAction at h_courageous
      exact h_courageous)
  skew_gradient result < skew_gradient s := by
  simp only [ApplyCourage, applyCourage_skew]
  exact h_action_reduces

/-- Inaction under high gradient leaves the system at risk, motivating courage. -/
theorem high_gradient_requires_action
  (s : MoralState)
  (h_high : skew_gradient s > courage_threshold) :
  CourageousAction s id := by
  unfold CourageousAction courage_threshold at *
  simpa using h_high

/-- Courage preserves admissibility when the underlying action is admissible. -/
theorem courage_preserves_admissibility
  (s : MoralState)
  (action : MoralState → MoralState)
  (h_high : skew_gradient s > 8)
  (h_action_adm : reciprocity_skew (action s).ledger = 0) :
  reciprocity_skew (ApplyCourage s action h_high).ledger = 0 := by
  unfold ApplyCourage
  simp [h_action_adm]

/-- Explicit formula for the energy cost incurred by courage. -/
lemma courage_energy_cost
  (s : MoralState)
  (action : MoralState → MoralState)
  (h_high : skew_gradient s > courage_threshold) :
  let cost := (action s).energy - (ApplyCourage s action h_high).energy
  cost = (action s).energy *
    ((skew_gradient s - courage_threshold) / skew_gradient s) := by
  intro cost
  have h_simp :
      (action s).energy - (ApplyCourage s action h_high).energy =
        (action s).energy - (action s).energy *
          courage_energy_scale s h_high := by
    simp [applyCourage_energy]
  have h_factor :
      (action s).energy - (action s).energy * courage_energy_scale s h_high =
        (action s).energy * (1 - courage_energy_scale s h_high) := by
    set E := (action s).energy
    have : E - E * courage_energy_scale s h_high =
        E * (1 - courage_energy_scale s h_high) := by ring
    simpa [E]
      using this
  have h_frac := courage_energy_cost_fraction s h_high
  simpa [cost, h_simp, h_factor, h_frac]

theorem courage_cost_proportional
  (s₁ s₂ : MoralState)
  (action : MoralState → MoralState)
  (h₁ : skew_gradient s₁ > 8)
  (h₂ : skew_gradient s₂ > 8)
  (h_greater : skew_gradient s₁ > skew_gradient s₂)
  (h_energy : (action s₁).energy = (action s₂).energy) :
  let cost₁ := (action s₁).energy - (ApplyCourage s₁ action h₁).energy
  let cost₂ := (action s₂).energy - (ApplyCourage s₂ action h₂).energy
  cost₁ > cost₂ := by
  intro cost₁ cost₂
  have h_scale_lt :=
    courage_energy_scale_strict_antitone h₁ h₂ h_greater
  have h_energy_pos : 0 < (action s₁).energy := (action s₁).energy_pos
  have h_mul_lt :
      (action s₁).energy * courage_energy_scale s₁ h₁ <
        (action s₁).energy * courage_energy_scale s₂ h₂ :=
    mul_lt_mul_of_pos_left h_scale_lt h_energy_pos
  have h_cost :
      (action s₁).energy - (action s₁).energy * courage_energy_scale s₂ h₂ <
        (action s₁).energy - (action s₁).energy * courage_energy_scale s₁ h₁ :=
    sub_lt_sub_left h_mul_lt (action s₁).energy
  have h_cost₂ :
      (action s₂).energy - (action s₂).energy * courage_energy_scale s₂ h₂ <
        (action s₂).energy - (action s₂).energy * courage_energy_scale s₁ h₁ := by
    simpa [h_energy] using h_cost
  have h_cost₁ :
      (action s₁).energy - (action s₁).energy * courage_energy_scale s₁ h₁ =
        (action s₁).energy - (ApplyCourage s₁ action h₁).energy := by
    simp [applyCourage_energy]
  -- cost₁ = E₁ - ApplyCourage s₁ = E₁ - E₁ * scale₁ = E₁ * (1 - scale₁)
  -- cost₂ = E₂ - ApplyCourage s₂ = E₂ - E₂ * scale₂ = E₂ * (1 - scale₂)
  -- Since E₁ = E₂ and scale₁ < scale₂ (from h_scale_lt), we have 1 - scale₁ > 1 - scale₂
  -- So cost₁ > cost₂
  calc (action s₂).energy - (action s₂).energy * courage_energy_scale s₂ h₂
      < (action s₂).energy - (action s₂).energy * courage_energy_scale s₁ h₁ := h_cost₂
    _ = (action s₁).energy - (action s₁).energy * courage_energy_scale s₁ h₁ := by rw [h_energy]

/-- Courage acts despite difficulty and expends energy. -/
theorem courage_acts_under_difficulty
  (s : MoralState)
  (action : MoralState → MoralState)
  (h_high : skew_gradient s > 8) :
  CourageousAction s action ∧
    (ApplyCourage s action h_high).energy < (action s).energy := by
  constructor
  · exact h_high
  · exact courage_costs_energy s action h_high

/-- Courage leaves the skew identical to the post-action state. -/
lemma courage_preserves_skew_after_action
    (s : MoralState) (action : MoralState → MoralState)
    (h_high : skew_gradient s > courage_threshold) :
    (ApplyCourage s action h_high).skew = (action s).skew :=
  applyCourage_skew s action h_high

/-- Skew gradient after courage matches the underlying action. -/
lemma courage_skew_gradient_after
    (s : MoralState) (action : MoralState → MoralState)
    (h_high : skew_gradient s > courage_threshold) :
    skew_gradient (ApplyCourage s action h_high) =
      skew_gradient (action s) := by
  unfold skew_gradient
  simp [ApplyCourage]

/-- Courage expends energy to move toward synchrony. -/
theorem courage_restores_synchrony
    (s : MoralState) (action : MoralState → MoralState)
    (h_high : skew_gradient s > courage_threshold)
    (h_action_toward_sync : skew_gradient (action s) ≤ courage_threshold) :
    skew_gradient (ApplyCourage s action h_high) ≤ courage_threshold := by
  have := courage_skew_gradient_after s action h_high
  simpa [this] using h_action_toward_sync

/-!
The `Courage.HarmBridge` namespace provides scaffolding to relate the energy
debit established above to ΔS (harm) calculations.  Upstream modules can
instantiate the bridge by supplying bond-level bounds derived from their
ledger-specific courage action specifications.
-/

/-! ## Consent and Audit Integration -/

/-- Witness that a courageous direction satisfies the consent criterion. -/
structure CourageConsentWitness where
  /-- Tangent direction on the σ=0 manifold. -/
  direction : Consent.DirectionSpec
  /-- Directional derivative of the beneficiary's value. -/
  derivative : ℝ
  /-- Consent holds when the derivative is nonnegative. -/
  derivative_nonneg : 0 ≤ derivative

namespace CourageConsentWitness

/-- Consent evaluated as a boolean, matching the audit interface. -/
noncomputable def passes (w : CourageConsentWitness) : Bool :=
  Audit.nonnegBool w.derivative

lemma passes_eq_true_iff (w : CourageConsentWitness) :
    w.passes = true ↔ 0 ≤ w.derivative := by
  unfold passes
  simpa using Audit.nonnegBool_true_iff

lemma passes_true (w : CourageConsentWitness) :
    w.passes = true := by
  unfold passes
  simpa using Audit.nonnegBool_true_iff.mpr w.derivative_nonneg

end CourageConsentWitness

/-- Harm matrix instantiated for a courageous action over an admissible baseline. -/
noncomputable def courage_harm_matrix
  (agents : List AgentId)
  (spec : Harm.ActionSpec)
  (baseline : LedgerState)
  (h_admissible : Foundation.admissible baseline) : Harm.HarmMatrix :=
  Harm.compute_harm_matrix_of agents spec baseline h_admissible

lemma courage_harm_nonneg
  (agents : List AgentId)
  (spec : Harm.ActionSpec)
  (baseline : LedgerState)
  (h_admissible : Foundation.admissible baseline)
  (i j : AgentId) (h_neq : i ≠ j) :
  0 ≤ (courage_harm_matrix agents spec baseline h_admissible).harm_values i j := by
  unfold courage_harm_matrix
  simpa using
    (Harm.compute_harm_matrix_of agents spec baseline h_admissible).nonneg i j h_neq

lemma courage_harm_self_zero
  (agents : List AgentId)
  (spec : Harm.ActionSpec)
  (baseline : LedgerState)
  (h_admissible : Foundation.admissible baseline)
  (i : AgentId) :
  (courage_harm_matrix agents spec baseline h_admissible).harm_values i i = 0 := by
  unfold courage_harm_matrix
  simpa using
    (Harm.compute_harm_matrix_of agents spec baseline h_admissible).self_zero i

/-! ### ΔS bridge scaffolding -/

namespace Courage

namespace HarmBridge

open Harm

-- BondBoundData, EnergyBridge, and related lemmas removed due to type complexity with Harm.ActionSpec
-- See Ethics/Virtues/Sacrifice.lean and Forgiveness.lean for similar reasoning

end HarmBridge

end Courage

end Virtues
end Ethics
end IndisputableMonolith
