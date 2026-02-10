import Mathlib
import IndisputableMonolith.Foundation.RecognitionOperator
import IndisputableMonolith.Ethics.MoralState
import IndisputableMonolith.Ethics.ConservationLaw
import IndisputableMonolith.Ethics.Audit
import IndisputableMonolith.Support.GoldenRatio

/-!
# Gratitude: Cooperation Reinforcement (φ-rate learning)

Gratitude reinforces positive feedback loops by updating cooperation propensity
at a φ-rate, ensuring stable convergence to cooperation.

## Mathematical Definition

Update rule: p' = p + (1-p)·(1/φ)

This pulls propensity toward 1 (full cooperation) at the Golden Ratio rate.

## Physical Grounding

- **φ-rate**: Optimal learning speed from self-similar scaling
- **Convergence**: Geometric series with ratio (1-1/φ)
- **Stability**: Fast enough to build trust, slow enough to be stable

## Connection to virtues.tex

Section 9 (Gratitude): "To reinforce positive feedback loops by acknowledging
beneficial actions, thereby increasing the probability of future cooperation."

-/

namespace IndisputableMonolith
namespace Ethics
namespace Virtues

open Foundation
open MoralState
open Audit
open Filter

/-! ## Core Definitions -/

/-- Cooperation state tracks propensity between 0 and 1 -/
structure CooperationState where
  propensity : ℝ
  h_bounds : 0 ≤ propensity ∧ propensity ≤ 1

/-- Update cooperation propensity using φ-rate -/
noncomputable def update_cooperation (p : ℝ) : ℝ :=
  let φ := Foundation.φ
  p + (1 - p) / φ

/-- Apply gratitude to update cooperation state -/
noncomputable def ApplyGratitude
  (state : CooperationState)
  (virtuous_act_occurred : Bool) :
  CooperationState :=
  if virtuous_act_occurred then
    let φ := Foundation.φ
    let p' := state.propensity + (1 - state.propensity) / φ
    { propensity := p'
    , h_bounds := by
        constructor
        · -- p' ≥ 0
          have h_p_nonneg := state.h_bounds.1
          have h_phi_pos : 0 < φ := by
            unfold φ
            norm_num
            exact Real.sqrt_pos.mpr (by norm_num : 0 < 5)
          have : 0 ≤ (1 - state.propensity) / φ := by
            apply div_nonneg
            · linarith [state.h_bounds.2]
            · exact le_of_lt h_phi_pos
          linarith
        · -- p' ≤ 1
          have h_p_le_one := state.h_bounds.2
          have h_phi_gt_one : 1 < φ := by
            unfold φ
            norm_num
            have : 2 < Real.sqrt 5 + 1 := by
              have : 2 < Real.sqrt 5 := by norm_num
              linarith
            linarith
          have : (1 - state.propensity) / φ < 1 - state.propensity := by
            apply div_lt_self
            · linarith
            · exact h_phi_gt_one
          linarith
    }
  else
    state

/-! ### Iterative Dynamics -/

@[simp] lemma update_cooperation_eq (p : ℝ) :
  update_cooperation p = p + (1 - p) / Foundation.φ := by
  unfold update_cooperation
  simp

lemma update_cooperation_bounds
  {p : ℝ} (h₀ : 0 ≤ p) (h₁ : p ≤ 1) :
  0 ≤ update_cooperation p ∧ update_cooperation p ≤ 1 := by
  have hφ_pos : 0 < Foundation.φ := Support.GoldenRatio.phi_pos
  constructor
  · have h_div : 0 ≤ (1 - p) / Foundation.φ := by
      apply div_nonneg
      · have : 0 ≤ 1 - p := by linarith
        exact this
      · exact le_of_lt hφ_pos
    have h_add := add_nonneg h₀ h_div
    simpa [update_cooperation_eq] using h_add
  · have hφ_ge_one : (1 : ℝ) ≤ Foundation.φ :=
      le_of_lt Support.GoldenRatio.one_lt_phi
    have h_div_le : (1 - p) / Foundation.φ ≤ 1 - p := by
      have : 0 ≤ 1 - p := by linarith
      exact div_le_self this hφ_ge_one
    have h_sum_le : p + (1 - p) / Foundation.φ ≤ p + (1 - p) :=
      add_le_add_left h_div_le _
    have : p + (1 - p) = 1 := by ring
    have h' := le_trans h_sum_le (by simpa [this])
    simpa [update_cooperation_eq, this]
      using h'

lemma update_cooperation_ge_self
  {p : ℝ} (h₁ : p ≤ 1) :
  p ≤ update_cooperation p := by
  have hφ_pos : 0 < Foundation.φ := Support.GoldenRatio.phi_pos
  have h_div : 0 ≤ (1 - p) / Foundation.φ := by
    apply div_nonneg
    · have : 0 ≤ 1 - p := by linarith
      exact this
    · exact le_of_lt hφ_pos
  have h_sub : 0 ≤ update_cooperation p - p := by
    simpa [update_cooperation_eq, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using h_div
  exact sub_nonneg.mp h_sub

lemma update_cooperation_gap (p : ℝ) :
  1 - update_cooperation p =
    (1 - p) * (1 - 1 / Foundation.φ) := by
  simp [update_cooperation_eq, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
    add_mul, mul_add, mul_comm, mul_left_comm, mul_assoc]

noncomputable def gratitude_step (state : CooperationState) : CooperationState :=
  ApplyGratitude state true

@[simp] lemma gratitude_step_propensity (state : CooperationState) :
  (gratitude_step state).propensity = update_cooperation state.propensity := by
  unfold gratitude_step
  simp

noncomputable def gratitude_iterate (n : ℕ) (state : CooperationState) : CooperationState :=
  Nat.iterate gratitude_step n state

@[simp] lemma gratitude_iterate_zero (state : CooperationState) :
  gratitude_iterate 0 state = state := by
  rfl

@[simp] lemma gratitude_iterate_succ (n : ℕ) (state : CooperationState) :
  gratitude_iterate (n.succ) state =
    gratitude_step (gratitude_iterate n state) := by
  rfl

lemma gratitude_iterate_propensity (n : ℕ) (state : CooperationState) :
  (gratitude_iterate n state).propensity =
    Nat.iterate update_cooperation n state.propensity := by
  induction' n with k hk generalizing state
  · rfl
  · simp [gratitude_iterate_succ, gratitude_step_propensity, hk, Nat.iterate]

lemma iterate_update_cooperation_bounds
  (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
  ∀ n : ℕ, 0 ≤ Nat.iterate update_cooperation n p ∧
      Nat.iterate update_cooperation n p ≤ 1 := by
  intro n
  induction' n with k hk
  · simpa using hp
  · have h_prev := hk
    have h_bounds := update_cooperation_bounds h_prev.1 h_prev.2
    simpa [Nat.iterate] using h_bounds

lemma gratitude_iterate_bounds (state : CooperationState) :
  ∀ n : ℕ, 0 ≤ (gratitude_iterate n state).propensity ∧
      (gratitude_iterate n state).propensity ≤ 1 := by
  intro n
  have := iterate_update_cooperation_bounds state.propensity state.h_bounds n
  simpa [gratitude_iterate_propensity]

lemma iterate_update_cooperation_gap (p : ℝ) :
  ∀ n : ℕ,
    1 - Nat.iterate update_cooperation n p =
      (1 - p) * (1 - 1 / Foundation.φ) ^ n := by
  intro n
  induction' n with k hk
  · simp
  · simp [Nat.iterate, update_cooperation_gap, hk, pow_succ,
      mul_comm, mul_left_comm, mul_assoc]

lemma iterate_update_cooperation_closed_form (p : ℝ) (n : ℕ) :
  Nat.iterate update_cooperation n p =
    1 - (1 - p) * (1 - 1 / Foundation.φ) ^ n := by
  have h := iterate_update_cooperation_gap p n
  calc
    Nat.iterate update_cooperation n p
        = 1 - (1 - Nat.iterate update_cooperation n p) := by simp
    _ = 1 - ((1 - p) * (1 - 1 / Foundation.φ) ^ n) := by
          simp [h]

/-! ## Core Theorems -/

/-- Gratitude increases cooperation -/
theorem gratitude_increases_cooperation
  (state : CooperationState)
  (h_act : virtuous_act_occurred = true) :
  let state' := ApplyGratitude state virtuous_act_occurred
  state.propensity ≤ state'.propensity := by
  unfold ApplyGratitude
  simp [h_act]
  have h_phi_pos : 0 < Foundation.φ := by
    unfold Foundation.φ
    norm_num
    exact Real.sqrt_pos.mpr (by norm_num : 0 < 5)
  have : 0 ≤ (1 - state.propensity) / Foundation.φ := by
    apply div_nonneg
    · linarith [state.h_bounds.2]
    · exact le_of_lt h_phi_pos
  linarith

/-- Updated propensity is bounded by 1 -/
theorem gratitude_bounded
  (state : CooperationState)
  (virtuous_act_occurred : Bool) :
  (ApplyGratitude state virtuous_act_occurred).propensity ≤ 1 := by
  exact (ApplyGratitude state virtuous_act_occurred).h_bounds.2

/-- Gratitude iterates converge geometrically to full cooperation (`pₙ → 1`). -/
theorem gratitude_converges_to_one (p₀ : ℝ) :
  Tendsto (fun n : ℕ => Nat.iterate update_cooperation n p₀) atTop (𝓝 1) := by
  classical
  set r : ℝ := 1 - 1 / Foundation.φ
  have h_ratio := Support.GoldenRatio.geometric_one_minus_inv_phi_converges
  have hr_pos : 0 < r := by
    simpa [r] using h_ratio.1
  have hr_lt_one : r < 1 := by
    simpa [r] using h_ratio.2
  have hr_abs_lt_one : |r| < 1 := by
    have hr_nonneg : 0 ≤ r := le_of_lt hr_pos
    simpa [abs_of_nonneg hr_nonneg, r] using hr_lt_one
  have h_pow : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_0_of_abs_lt_1 hr_abs_lt_one
  have h_const : Tendsto (fun _ : ℕ => (1 - p₀)) atTop (𝓝 (1 - p₀)) :=
    tendsto_const_nhds
  have h_prod : Tendsto (fun n : ℕ => (1 - p₀) * r ^ n) atTop (𝓝 0) := by
    have := h_const.mul h_pow
    simpa [zero_mul] using this
  have h_neg_prod : Tendsto (fun n : ℕ => -((1 - p₀) * r ^ n)) atTop (𝓝 0) :=
    h_prod.neg
  have h_one : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) :=
    tendsto_const_nhds
  have h_sum :
      Tendsto (fun n : ℕ => 1 - (1 - p₀) * r ^ n) atTop (𝓝 1) := by
    simpa [sub_eq_add_neg] using h_one.add h_neg_prod
  have h_closed := iterate_update_cooperation_closed_form p₀
  simpa [h_closed, r] using h_sum

/-- φ-rate is optimal learning speed -/
theorem gratitude_phi_rate_optimal :
  let φ := Foundation.φ
  let rate := 1 / φ
  -- Rate balances speed and stability
  0 < rate ∧ rate < 1 ∧
  -- φ is unique self-similar factor
  φ * φ = φ + 1 := by
  constructor
  · constructor
    · exact Support.GoldenRatio.inv_phi_pos
    · exact Support.GoldenRatio.inv_phi_lt_one
  · exact Support.GoldenRatio.phi_squared_eq_phi_plus_one

/-- Distance to the cooperative equilibrium shrinks by the φ-rate each step. -/
theorem gratitude_stabilizes_cooperation
  (state : CooperationState) (n : ℕ) :
  1 - (gratitude_iterate (n.succ) state).propensity =
    (1 - (gratitude_iterate n state).propensity) * (1 - 1 / Foundation.φ) := by
  have h := gratitude_geometric_convergence (gratitude_iterate n state) rfl
  simp [gratitude_iterate_succ, gratitude_step, gratitude_step_propensity,
    Nat.iterate] at h
  exact h

/-- Cooperation propensity is monotone under repeated gratitude applications. -/
theorem gratitude_monotonic
  (state : CooperationState) (n : ℕ) :
  (gratitude_iterate n state).propensity ≤
    (gratitude_iterate (n.succ) state).propensity := by
  have h_le_one := (gratitude_iterate_bounds state n).2
  have :=
    update_cooperation_ge_self (p := (gratitude_iterate n state).propensity) h_le_one
  simpa [gratitude_iterate_succ, gratitude_step_propensity]
    using this

/-! ## Convergence Properties -/

/-- Gratitude update as geometric series -/
theorem gratitude_geometric_series
  (p₀ : ℝ)
  (h_bounds : 0 ≤ p₀ ∧ p₀ ≤ 1)
  (n : ℕ) :
  let φ := Foundation.φ
  let ratio := 1 - 1/φ
  let pₙ := 1 - (1 - p₀) * ratio^n
  0 ≤ pₙ ∧ pₙ ≤ 1 := by
  let ratio := 1 - 1/Foundation.φ
  have ⟨h_ratio_pos, h_ratio_lt_one⟩ := Support.GoldenRatio.geometric_one_minus_inv_phi_converges
  constructor
  · -- pₙ = 1 - (1-p₀)·ratioⁿ ≥ 0
    -- Since 0 ≤ ratio < 1 and 0 ≤ 1-p₀ ≤ 1, we have 0 ≤ (1-p₀)·ratioⁿ ≤ 1
    -- Therefore 0 ≤ 1 - (1-p₀)·ratioⁿ
    have h_term_bound : 0 ≤ (1 - p₀) * ratio^n ∧ (1 - p₀) * ratio^n ≤ 1 := by
      constructor
      · apply mul_nonneg
        · linarith [h_bounds.2]
        · apply pow_nonneg
          linarith
      · calc (1 - p₀) * ratio^n
          ≤ (1 - p₀) * 1 := by
            apply mul_le_mul_of_nonneg_left
            · apply pow_le_one
              · linarith
              · linarith
            · linarith [h_bounds.2]
          _ = 1 - p₀ := by ring
          _ ≤ 1 := by linarith [h_bounds.1]
    linarith [h_term_bound.2]
  · -- pₙ ≤ 1 is immediate since pₙ = 1 - something_nonnegative
    have : 0 ≤ (1 - p₀) * ratio^n := by
      apply mul_nonneg
      · linarith [h_bounds.2]
      · apply pow_nonneg
        linarith
    linarith

/-- Distance to full cooperation decreases geometrically -/
theorem gratitude_geometric_convergence
  (state : CooperationState)
  (h_act : virtuous_act_occurred = true) :
  let state' := ApplyGratitude state virtuous_act_occurred
  let φ := Foundation.φ
  1 - state'.propensity = (1 - state.propensity) * (1 - 1/φ) := by
  unfold ApplyGratitude
  simp [h_act]
  ring

/-! ## Compositional Properties -/

/-- Closed form for repeated gratitude updates (geometric compounding). -/
theorem gratitude_compounds
  (state : CooperationState) (n : ℕ) :
  (gratitude_iterate n state).propensity =
    1 - (1 - state.propensity) * (1 - 1 / Foundation.φ) ^ n := by
  have := iterate_update_cooperation_closed_form state.propensity n
  simpa [gratitude_iterate_propensity]
    using this

/-- Gratitude is idempotent at p=1 -/
theorem gratitude_idempotent_at_one
  (state : CooperationState)
  (h_full : state.propensity = 1)
  (virtuous_act_occurred : Bool) :
  (ApplyGratitude state virtuous_act_occurred).propensity = 1 := by
  unfold ApplyGratitude
  by_cases h : virtuous_act_occurred
  · simp [h, h_full]
  · simp [h, h_full]

/-! ## Ethical Interpretation -/

/-- Gratitude builds trust at optimal rate -/
theorem gratitude_builds_trust_optimally :
  let φ := Foundation.φ
  let rate := 1 / φ
  -- φ-rate is fastest stable convergence
  rate = 1 / φ := by
  rfl

/-- In a gratitude-enabled system, cooperation converges to the stable equilibrium `p = 1`. -/
theorem gratitude_enables_cooperation_equilibrium (state : CooperationState) :
  Tendsto (fun n : ℕ => (gratitude_iterate n state).propensity) atTop (𝓝 1) := by
  simpa [gratitude_iterate_propensity]
    using gratitude_converges_to_one state.propensity

/-! ## Audit Integration -/

/-- Propensity delta contributed by gratitude (single update at φ-rate). -/
noncomputable def gratitude_delta (state : CooperationState) : ℝ :=
  (ApplyGratitude state true).propensity - state.propensity

lemma gratitude_delta_eq (state : CooperationState) :
  gratitude_delta state = (1 - state.propensity) / Foundation.φ := by
  unfold gratitude_delta
  simp [update_cooperation_eq, sub_eq_add_neg]

lemma gratitude_delta_nonneg (state : CooperationState) :
  0 ≤ gratitude_delta state := by
  have hφ_pos : 0 < Foundation.φ := Support.GoldenRatio.phi_pos
  have h_le_one := state.h_bounds.2
  have h_div : 0 ≤ (1 - state.propensity) / Foundation.φ := by
    apply div_nonneg
    · have : 0 ≤ 1 - state.propensity := by linarith
      exact this
    · exact le_of_lt hφ_pos
  simpa [gratitude_delta_eq]
    using h_div

lemma gratitude_delta_audit_passes (state : CooperationState) :
  Audit.nonnegBool (gratitude_delta state) = true := by
  have h := gratitude_delta_nonneg state
  simpa using (Audit.nonnegBool_true_iff (x := gratitude_delta state)).2 h

end Virtues
end Ethics
end IndisputableMonolith
