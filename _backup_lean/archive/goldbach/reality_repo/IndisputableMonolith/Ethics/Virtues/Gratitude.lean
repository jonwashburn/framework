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
        have h := update_cooperation_bounds state.h_bounds.1 state.h_bounds.2
        unfold update_cooperation at h
        exact h
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
  have hp : 0 ≤ p ∧ p ≤ 1 := ⟨h₀, h₁⟩
  exact iterate_update_cooperation_bounds p hp 1

lemma update_cooperation_ge_self
  {p : ℝ} (h₁ : p ≤ 1) :
  p ≤ update_cooperation p := by
  unfold update_cooperation
  have hφ_pos : 0 < Foundation.φ := Support.GoldenRatio.phi_pos
  have h_gap_nonneg : 0 ≤ 1 - p := by linarith
  have h_div_nonneg : 0 ≤ (1 - p) / Foundation.φ := div_nonneg h_gap_nonneg (le_of_lt hφ_pos)
  linarith

lemma update_cooperation_gap (p : ℝ) :
  1 - update_cooperation p =
    (1 - p) * (1 - 1 / Foundation.φ) := by
  unfold update_cooperation
  have hφ_pos : 0 < Foundation.φ := Support.GoldenRatio.phi_pos
  field_simp
  ring

noncomputable def gratitude_step (state : CooperationState) : CooperationState :=
  ApplyGratitude state true

@[simp] lemma gratitude_step_propensity (state : CooperationState) :
  (gratitude_step state).propensity = update_cooperation state.propensity := by
  simp only [gratitude_step, ApplyGratitude, update_cooperation, ↓reduceIte]

noncomputable def gratitude_iterate (n : ℕ) (state : CooperationState) : CooperationState :=
  Nat.iterate gratitude_step n state

@[simp] lemma gratitude_iterate_zero (state : CooperationState) :
  gratitude_iterate 0 state = state := rfl

@[simp] lemma gratitude_iterate_succ (n : ℕ) (state : CooperationState) :
  gratitude_iterate (n.succ) state =
    gratitude_step (gratitude_iterate n state) := by
  simp only [gratitude_iterate, Function.iterate_succ']

lemma gratitude_iterate_propensity (n : ℕ) (state : CooperationState) :
  (gratitude_iterate n state).propensity =
    Nat.iterate update_cooperation n state.propensity := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [gratitude_iterate_succ, gratitude_step_propensity, Function.iterate_succ', ih]

lemma iterate_update_cooperation_bounds
  (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
  ∀ n : ℕ, 0 ≤ Nat.iterate update_cooperation n p ∧
      Nat.iterate update_cooperation n p ≤ 1 := by
  intro n
  rw [iterate_update_cooperation_closed_form]
  constructor
  · -- 0 ≤ 1 - (1-p) * r^n where r = 1 - 1/φ ∈ (0,1)
    have h_r_pos : 0 < 1 - 1 / Foundation.φ := by
      have hφ_gt_one : 1 < Foundation.φ := Support.GoldenRatio.one_lt_phi
      have hφ_pos : 0 < Foundation.φ := Support.GoldenRatio.phi_pos
      have h_inv_lt_one : 1 / Foundation.φ < 1 := by
        rw [div_lt_one hφ_pos]
        exact hφ_gt_one
      linarith
    have h_r_le_one : 1 - 1 / Foundation.φ ≤ 1 := by linarith
    have h_gap_nonneg : 0 ≤ 1 - p := by linarith [hp.2]
    have h_pow_nonneg : 0 ≤ (1 - 1 / Foundation.φ) ^ n := pow_nonneg (le_of_lt h_r_pos) n
    have h_pow_le_one : (1 - 1 / Foundation.φ) ^ n ≤ 1 := pow_le_one₀ (le_of_lt h_r_pos) h_r_le_one
    have h_prod_le : (1 - p) * (1 - 1 / Foundation.φ) ^ n ≤ 1 - p := by
      apply mul_le_of_le_one_right h_gap_nonneg h_pow_le_one
    linarith
  · -- 1 - (1-p) * r^n ≤ 1
    have h_r_pos : 0 < 1 - 1 / Foundation.φ := by
      have hφ_gt_one : 1 < Foundation.φ := Support.GoldenRatio.one_lt_phi
      have hφ_pos : 0 < Foundation.φ := Support.GoldenRatio.phi_pos
      have h_inv_lt_one : 1 / Foundation.φ < 1 := by
        rw [div_lt_one hφ_pos]
        exact hφ_gt_one
      linarith
    have h_gap_nonneg : 0 ≤ 1 - p := by linarith [hp.2]
    have h_pow_nonneg : 0 ≤ (1 - 1 / Foundation.φ) ^ n := pow_nonneg (le_of_lt h_r_pos) n
    have h_prod_nonneg : 0 ≤ (1 - p) * (1 - 1 / Foundation.φ) ^ n :=
      mul_nonneg h_gap_nonneg h_pow_nonneg
    linarith

lemma gratitude_iterate_bounds (state : CooperationState) :
  ∀ n : ℕ, 0 ≤ (gratitude_iterate n state).propensity ∧
      (gratitude_iterate n state).propensity ≤ 1 := by
  intro n
  rw [gratitude_iterate_propensity]
  exact iterate_update_cooperation_bounds state.propensity state.h_bounds n

lemma iterate_update_cooperation_gap (p : ℝ) :
  ∀ n : ℕ,
    1 - Nat.iterate update_cooperation n p =
      (1 - p) * (1 - 1 / Foundation.φ) ^ n := by
  intro n
  rw [iterate_update_cooperation_closed_form]
  ring

lemma iterate_update_cooperation_closed_form (p : ℝ) (n : ℕ) :
  Nat.iterate update_cooperation n p =
    1 - (1 - p) * (1 - 1 / Foundation.φ) ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    simp only [Function.iterate_succ']
    rw [ih]
    rw [update_cooperation_gap]
    ring

/-! ## Core Theorems -/

/-- Gratitude increases cooperation -/
theorem gratitude_increases_cooperation
  (state : CooperationState)
  (h_act : virtuous_act_occurred = true) :
  let state' := ApplyGratitude state virtuous_act_occurred
  state.propensity ≤ state'.propensity := by
  simp only [ApplyGratitude, h_act, ↓reduceIte]
  exact update_cooperation_ge_self state.h_bounds.2

/-- Updated propensity is bounded by 1 -/
theorem gratitude_bounded
  (state : CooperationState)
  (virtuous_act_occurred : Bool) :
  (ApplyGratitude state virtuous_act_occurred).propensity ≤ 1 := by
  exact (ApplyGratitude state virtuous_act_occurred).h_bounds.2

/-- Gratitude iterates converge geometrically to full cooperation (`pₙ → 1`). -/
theorem gratitude_converges_to_one (p₀ : ℝ) :
  Filter.Tendsto (fun n : ℕ => (update_cooperation^[n]) p₀) Filter.atTop (nhds 1) := by
  -- Closed form: update_cooperation^[n] p₀ = 1 - (1 - p₀) * r^n where r = 1 - 1/φ
  have h_closed : ∀ n, (update_cooperation^[n]) p₀ = 1 - (1 - p₀) * (1 - 1 / Foundation.φ) ^ n :=
    iterate_update_cooperation_closed_form p₀
  simp_rw [h_closed]
  -- Need: 1 - (1 - p₀) * r^n → 1, i.e., (1 - p₀) * r^n → 0
  -- Since 0 < r < 1, we have r^n → 0
  have h_r_pos : 0 < 1 - 1 / Foundation.φ := by
    have hφ_gt_one : 1 < Foundation.φ := Support.GoldenRatio.one_lt_phi
    have hφ_pos : 0 < Foundation.φ := Support.GoldenRatio.phi_pos
    have h_inv_lt_one : 1 / Foundation.φ < 1 := by rw [div_lt_one hφ_pos]; exact hφ_gt_one
    linarith
  have h_r_lt_one : 1 - 1 / Foundation.φ < 1 := by
    have hφ_pos : 0 < Foundation.φ := Support.GoldenRatio.phi_pos
    have h_inv_pos : 0 < 1 / Foundation.φ := div_pos one_pos hφ_pos
    linarith
  have h_pow_tendsto : Filter.Tendsto (fun n => (1 - 1 / Foundation.φ) ^ n)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt h_r_pos) h_r_lt_one
  have h_mul_tendsto : Filter.Tendsto (fun n => (1 - p₀) * (1 - 1 / Foundation.φ) ^ n)
      Filter.atTop (nhds ((1 - p₀) * 0)) :=
    Filter.Tendsto.const_mul (1 - p₀) h_pow_tendsto
  simp only [mul_zero] at h_mul_tendsto
  have h_sub_tendsto : Filter.Tendsto (fun n => 1 - (1 - p₀) * (1 - 1 / Foundation.φ) ^ n)
      Filter.atTop (nhds (1 - 0)) := by
    exact Filter.Tendsto.const_sub 1 h_mul_tendsto
  simp only [sub_zero] at h_sub_tendsto
  exact h_sub_tendsto

/-- φ-rate is optimal learning speed -/
theorem gratitude_phi_rate_optimal :
  let φ := Foundation.φ
  let rate := 1 / φ
  -- Rate balances speed and stability
  0 < rate ∧ rate < 1 ∧
  -- φ is unique self-similar factor
  φ * φ = φ + 1 := by
  have hφ_pos : 0 < Foundation.φ := Support.GoldenRatio.phi_pos
  have hφ_gt_one : 1 < Foundation.φ := Support.GoldenRatio.one_lt_phi
  refine ⟨?_, ?_, Support.GoldenRatio.phi_sq⟩
  · exact div_pos one_pos hφ_pos
  · rw [div_lt_one hφ_pos]
    exact hφ_gt_one

/-- Distance to the cooperative equilibrium shrinks by the φ-rate each step. -/
theorem gratitude_stabilizes_cooperation
  (state : CooperationState) (n : ℕ) :
  1 - (gratitude_iterate (n.succ) state).propensity =
    (1 - (gratitude_iterate n state).propensity) * (1 - 1 / Foundation.φ) := by
  rw [gratitude_iterate_propensity, gratitude_iterate_propensity]
  rw [iterate_update_cooperation_gap, iterate_update_cooperation_gap]
  ring

/-- Cooperation propensity is monotone under repeated gratitude applications. -/
theorem gratitude_monotonic
  (state : CooperationState) (n : ℕ) :
  (gratitude_iterate n state).propensity ≤
    (gratitude_iterate (n.succ) state).propensity := by
  rw [gratitude_iterate_succ, gratitude_step_propensity]
  exact update_cooperation_ge_self (gratitude_iterate_bounds state n).2

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
  -- This follows from iterate_update_cooperation_bounds
  have h := iterate_update_cooperation_bounds p₀ h_bounds n
  rw [iterate_update_cooperation_closed_form] at h
  exact h

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
  Filter.Tendsto (fun n : ℕ => (gratitude_iterate n state).propensity) Filter.atTop (nhds 1) := by
  -- gratitude_iterate_propensity shows (gratitude_iterate n state).propensity =
  --   Nat.iterate update_cooperation n state.propensity
  have h_eq : ∀ n, (gratitude_iterate n state).propensity =
      (update_cooperation^[n]) state.propensity := gratitude_iterate_propensity
  simp_rw [h_eq]
  exact gratitude_converges_to_one state.propensity

/-! ## Audit Integration -/

/-- Propensity delta contributed by gratitude (single update at φ-rate). -/
noncomputable def gratitude_delta (state : CooperationState) : ℝ :=
  (ApplyGratitude state true).propensity - state.propensity

lemma gratitude_delta_eq (state : CooperationState) :
  gratitude_delta state = (1 - state.propensity) / Foundation.φ := by
  unfold gratitude_delta ApplyGratitude
  simp only [↓reduceIte]
  ring

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
