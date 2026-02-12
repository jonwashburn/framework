import Mathlib
import IndisputableMonolith.Foundation.RecognitionOperator
import IndisputableMonolith.Ethics.MoralState
import IndisputableMonolith.Ethics.ConservationLaw
import IndisputableMonolith.Support.GoldenRatio
import IndisputableMonolith.Ethics.Virtues.Wisdom

/-!
# Patience: Respect for the Natural Time Constant

Patience ensures that agents respect the fundamental discrete time scale of
reality (the "eight-beat" or "breath period"), allowing Wisdom sufficient
observation windows to converge.

## Mathematical Definition

For an action a:
1. **Wait** at least `patience_threshold` (τ₀ = 8 ticks) since last action
2. **Observe** the full cycle of consequences
3. **Act** only when the cycle completes

## Physical Grounding

- **Discrete Time**: Reality updates in discrete ticks (τ₀)
- **Information Horizon**: Convergence requires observation over at least one full period
- **Z-oscillation**: The fundamental Z-zitterbewegung has period 8; actions faster than
  this disrupt the vacuum state.

## Connection to virtues.tex

Section 5 (Patience): "To respect the natural time constant of the system, acting
only when observation has converged."

Key property: `patience_implements_wisdom` - observation window matches Wisdom's requirements

-/

namespace IndisputableMonolith
namespace Ethics
namespace Virtues

open Foundation
open MoralState

/-- The fundamental patience threshold (8 ticks). -/
def patience_threshold : ℕ := 8

/-- Predicate: has sufficient time elapsed? -/
def is_patient (time_executed time_last_action : ℕ) : Prop :=
  time_executed - time_last_action ≥ patience_threshold

/-- Structure tracking timing of moral actions. -/
structure TimedAction where
  /-- Time of execution (ticks since epoch). -/
  time_executed : ℕ
  /-- Time of previous action (ticks since epoch). -/
  time_last_action : ℕ
  /-- Proof: Actions are ordered in time. -/
  time_order : time_last_action ≤ time_executed

/-- A timed action is CycleAligned if it lands on an integer multiple of the period. -/
def CycleAligned (a : TimedAction) : Prop :=
  ∃ n > 0, a.time_executed = a.time_last_action + n * patience_threshold

/-- Window of observations available to Wisdom between actions. -/
def observationWindow (stream : ℕ → MoralState) (start_time : ℕ) : List MoralState :=
  (List.range patience_threshold).map (fun offset => stream (start_time + offset))

namespace TimedAction

/-- Inter-arrival time (wait duration). -/
def interArrival (a : TimedAction) : ℕ :=
  a.time_executed - a.time_last_action

lemma interArrival_ge_of_patient
    (a : TimedAction)
    (h_patient : is_patient a.time_executed a.time_last_action) :
    a.interArrival ≥ patience_threshold :=
  h_patient

lemma last_le_exec_of_patient
    (a : TimedAction)
    (h_patient : is_patient a.time_executed a.time_last_action) :
    a.time_last_action ≤ a.time_executed :=
  a.time_order

lemma time_eq_last_add_interArrival
    (a : TimedAction)
    (h_patient : is_patient a.time_executed a.time_last_action) :
    a.time_executed = a.time_last_action + a.interArrival := by
  unfold interArrival
  have h_order := a.time_order
  omega

lemma interArrival_decompose
    (a : TimedAction)
    (h_patient : is_patient a.time_executed a.time_last_action) :
    ∃ extra : ℕ, a.interArrival = patience_threshold + extra := by
  unfold is_patient at h_patient
  unfold interArrival
  use a.time_executed - a.time_last_action - patience_threshold
  omega

/-- Penalty for acting before the patience threshold (zero when patient). -/
def impatiencePenalty (a : TimedAction) : ℕ :=
  patience_threshold - min patience_threshold a.interArrival

lemma impatiencePenalty_eq_zero_of_patient
    (a : TimedAction)
    (h_patient : is_patient a.time_executed a.time_last_action) :
    a.impatiencePenalty = 0 := by
  unfold impatiencePenalty
  have h_ge := interArrival_ge_of_patient a h_patient
  rw [min_eq_left h_ge]
  omega

lemma impatiencePenalty_pos_of_impatient
    (a : TimedAction)
    (h_impatient : ¬ is_patient a.time_executed a.time_last_action) :
    0 < a.impatiencePenalty := by
  unfold impatiencePenalty
  unfold is_patient at h_impatient
  push_neg at h_impatient
  -- h_impatient : interArrival a < patience_threshold
  have h_lt : a.interArrival < patience_threshold := h_impatient
  rw [min_eq_right (le_of_lt h_lt)]
  omega

end TimedAction

/-- Helper lemma: foldl with addition admits extraction of an initial constant. -/
private lemma foldl_add_const {α : Type _}
    (xs : List α) (f : α → ℕ) (acc : ℕ) :
    xs.foldl (fun n x => n + f x) acc =
      acc + xs.foldl (fun n x => n + f x) 0 := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih (acc + f x), ih (0 + f x)]
    omega

/-- Total waiting time accumulated by a list of timed actions. -/
def totalWait (actions : List TimedAction) : ℕ :=
  actions.foldl (fun acc action => acc + action.interArrival) 0

@[simp] lemma totalWait_nil : totalWait [] = 0 := rfl

lemma totalWait_cons (a : TimedAction) (actions : List TimedAction) :
    totalWait (a :: actions) = a.interArrival + totalWait actions := by
  unfold totalWait
  simp only [List.foldl_cons]
  rw [foldl_add_const]
  omega

/-- Aggregate impatience penalty for a list of actions. -/
def cumulativePenalty (actions : List TimedAction) : ℕ :=
  actions.foldl (fun acc action => acc + action.impatiencePenalty) 0

@[simp] lemma cumulativePenalty_nil : cumulativePenalty [] = 0 := rfl

lemma cumulativePenalty_cons (a : TimedAction) (actions : List TimedAction) :
    cumulativePenalty (a :: actions) =
      a.impatiencePenalty + cumulativePenalty actions := by
  unfold cumulativePenalty
  simp only [List.foldl_cons]
  rw [foldl_add_const]
  omega

lemma cumulativePenalty_patient_zero
    (actions : List TimedAction)
    (h_patient : ∀ a ∈ actions, is_patient a.time_executed a.time_last_action) :
    cumulativePenalty actions = 0 := by
  induction actions with
  | nil => rfl
  | cons a as ih =>
    rw [cumulativePenalty_cons]
    have h_a : is_patient a.time_executed a.time_last_action := by
      apply h_patient
      simp only [List.mem_cons, true_or]
    have h_as : ∀ a' ∈ as, is_patient a'.time_executed a'.time_last_action := by
      intro a' ha'
      apply h_patient
      simp only [List.mem_cons]
      right; exact ha'
    rw [TimedAction.impatiencePenalty_eq_zero_of_patient a h_a, ih h_as]

lemma cumulativePenalty_pos_of_impatient
    (actions : List TimedAction)
    (h_impatient : ∃ a ∈ actions, ¬ is_patient a.time_executed a.time_last_action) :
    0 < cumulativePenalty actions := by
  obtain ⟨a, ha_mem, ha_impatient⟩ := h_impatient
  induction actions with
  | nil => simp at ha_mem
  | cons x xs ih =>
    rw [cumulativePenalty_cons]
    simp only [List.mem_cons] at ha_mem
    cases ha_mem with
    | inl h_eq =>
      -- a = x, so x is impatient
      subst h_eq
      have h_pos := TimedAction.impatiencePenalty_pos_of_impatient a ha_impatient
      omega
    | inr h_in_xs =>
      -- a ∈ xs
      have ih_applied := ih h_in_xs
      omega

/-- Total wait time is bounded below by patience threshold for patient agents. -/
theorem totalWait_ge_of_patient
    (actions : List TimedAction)
    (h_patient : ∀ a ∈ actions, is_patient a.time_executed a.time_last_action) :
    patience_threshold * actions.length ≤ totalWait actions := by
  induction actions with
  | nil => simp [totalWait_nil]
  | cons a as ih =>
    rw [totalWait_cons, List.length_cons]
    have h_a : is_patient a.time_executed a.time_last_action := by
      apply h_patient
      simp only [List.mem_cons, true_or]
    have h_as : ∀ a' ∈ as, is_patient a'.time_executed a'.time_last_action := by
      intro a' ha'
      apply h_patient
      simp only [List.mem_cons]
      right; exact ha'
    have h_ge := TimedAction.interArrival_ge_of_patient a h_a
    have ih_applied := ih h_as
    -- patience_threshold * (as.length + 1) ≤ a.interArrival + totalWait as
    -- = patience_threshold * as.length + patience_threshold
    calc patience_threshold * (as.length + 1)
        = patience_threshold * as.length + patience_threshold := by ring
      _ ≤ totalWait as + patience_threshold := by omega
      _ ≤ totalWait as + a.interArrival := by omega
      _ = a.interArrival + totalWait as := by ring

/-- Total wait time is strictly less than minimal patience requirement for uniformly impatient agents. -/
theorem totalWait_lt_of_impatient
    (actions : List TimedAction)
    (h_impatient : ∀ a ∈ actions, ¬ is_patient a.time_executed a.time_last_action)
    (h_nonempty : actions ≠ []) :
    totalWait actions < patience_threshold * actions.length := by
  induction actions with
  | nil => contradiction
  | cons a as ih =>
    rw [totalWait_cons, List.length_cons]
    have h_a_impatient := h_impatient a (List.mem_cons_self a as)
    unfold is_patient at h_a_impatient
    simp only [not_le] at h_a_impatient
    have h_a_bound : a.interArrival < patience_threshold := h_a_impatient
    by_cases h_as_empty : as = []
    · simp [h_as_empty, totalWait]
      calc a.interArrival
          < patience_threshold := h_a_bound
        _ = patience_threshold * 1 := by ring
    · have h_as_impatient : ∀ a' ∈ as, ¬ is_patient a'.time_executed a'.time_last_action := by
        intro a' ha'
        exact h_impatient a' (List.mem_cons_of_mem a ha')
      have h_ih := ih h_as_impatient h_as_empty
      calc a.interArrival + totalWait as
          < patience_threshold + patience_threshold * as.length := by
            apply Nat.add_lt_add h_a_bound h_ih
        _ = patience_threshold * (as.length + 1) := by ring

/-! ## Wisdom integration -/

/-- Range monotonicity helper. -/
lemma range_subset_of_le {m n : ℕ} (h : m ≤ n) :
    Finset.range m ⊆ Finset.range n := by
  intro x hx
  simp only [Finset.mem_range] at hx ⊢
  omega

/-- Shortened observation windows miss at least one tick of the patience cycle. -/
theorem patience_eight_tick_optimal
    (subset : Finset ℕ)
    (h_subset : subset ⊆ Finset.range patience_threshold)
    (h_card : subset.card < patience_threshold) :
    ∃ tick ∈ Finset.range patience_threshold, tick ∉ subset := by
  -- If subset.card < patience_threshold and subset ⊆ range patience_threshold,
  -- then subset is a proper subset of range patience_threshold
  by_contra h
  push_neg at h
  -- h : ∀ tick ∈ range patience_threshold, tick ∈ subset
  -- This means range patience_threshold ⊆ subset
  have h_range_sub : Finset.range patience_threshold ⊆ subset := by
    intro x hx
    exact h x hx
  -- So subset = range patience_threshold (since subset ⊆ range patience_threshold)
  have h_eq : subset = Finset.range patience_threshold := by
    exact Finset.Subset.antisymm h_subset h_range_sub
  -- But then subset.card = patience_threshold
  rw [h_eq, Finset.card_range] at h_card
  -- Contradiction: patience_threshold < patience_threshold
  omega

/-- Impatient schedules leave some tick of the patience cycle unobserved. -/
theorem impatient_missing_tick
    (timed_action : TimedAction)
    (h_impatient : ¬ is_patient timed_action.time_executed timed_action.time_last_action)
    (h_time_order : timed_action.time_last_action ≤ timed_action.time_executed) :
    ∃ missing < patience_threshold,
      timed_action.time_executed ≤ timed_action.time_last_action + missing := by
  unfold is_patient at h_impatient
  push_neg at h_impatient
  -- h_impatient : time_executed - time_last_action < patience_threshold
  use timed_action.time_executed - timed_action.time_last_action
  constructor
  · exact h_impatient
  · omega

/-- Re-ordering patient observations does not change Wisdom's φ-weighted skew. -/
theorem patience_enables_wisdom
    (s : MoralState)
    (stream : ℕ → MoralState)
    (timed_action : TimedAction)
    (choices : List MoralState)
    (h_perm : choices.Perm (observationWindow stream timed_action.time_last_action)) :
    (Int.natAbs (WiseChoice s choices).skew : ℝ) =
      (Int.natAbs (WiseChoice s (observationWindow stream timed_action.time_last_action)).skew : ℝ) := by
  -- Use wisdom_stable_under_permutation
  have h := Wisdom.wisdom_stable_under_permutation s choices
    (observationWindow stream timed_action.time_last_action) h_perm
  simp only at h
  -- h says score₁ * weight = score₂ * weight
  -- Since weight > 0, this means score₁ = score₂
  have h_weight_pos : 0 < 1 / (1 + Foundation.φ) := by
    apply div_pos one_pos
    have := Support.GoldenRatio.phi_pos
    linarith
  exact mul_right_cancel₀ (ne_of_gt h_weight_pos) h

/-- Periodic extension lemma: repeating patience cycles leaves the stream unchanged. -/
lemma periodic_shift
    (stream : ℕ → MoralState)
    (h_periodic : ∀ n, stream (n + patience_threshold) = stream n) :
    ∀ cycles n, stream (n + patience_threshold * cycles) = stream n := by
  intro cycles
  induction cycles with
  | zero => simp
  | succ k ih =>
    intro n
    calc stream (n + patience_threshold * (k + 1))
        = stream (n + patience_threshold * k + patience_threshold) := by ring_nf
      _ = stream (n + patience_threshold * k) := h_periodic _
      _ = stream n := ih n

/-- Cycle-aligned patient windows present identical information to Wisdom. -/
theorem patience_implements_wisdom
    (s : MoralState)
    (stream : ℕ → MoralState)
    (timed_action : TimedAction)
    (h_aligned : CycleAligned timed_action)
    (h_periodic : ∀ n, stream (n + patience_threshold) = stream n) :
    observationWindow stream timed_action.time_executed =
      observationWindow stream timed_action.time_last_action := by
  -- CycleAligned means time_executed = time_last_action + k * patience_threshold
  unfold CycleAligned at h_aligned
  obtain ⟨k, hk⟩ := h_aligned
  unfold observationWindow
  ext i
  simp only [List.mem_map, Finset.mem_range]
  constructor
  · intro ⟨j, hj_lt, hj_eq⟩
    use j, hj_lt
    rw [← hj_eq]
    have h_shift : timed_action.time_executed + j = timed_action.time_last_action + j + patience_threshold * k := by
      omega
    rw [h_shift]
    exact (periodic_shift stream h_periodic k (timed_action.time_last_action + j)).symm
  · intro ⟨j, hj_lt, hj_eq⟩
    use j, hj_lt
    rw [← hj_eq]
    have h_shift : timed_action.time_executed + j = timed_action.time_last_action + j + patience_threshold * k := by
      omega
    rw [h_shift]
    exact periodic_shift stream h_periodic k (timed_action.time_last_action + j)

/-- Patient moral agents invest at least the cadence time per action, impatient ones do not. -/
theorem patience_long_term_thinking
    (patient_agent impatient_agent : List TimedAction)
    (h_patient : ∀ a ∈ patient_agent, is_patient a.time_executed a.time_last_action)
    (h_impatient : ∀ a ∈ impatient_agent, ¬ is_patient a.time_executed a.time_last_action) :
    patience_threshold * patient_agent.length ≤ totalWait patient_agent ∧
      (impatient_agent ≠ [] → totalWait impatient_agent < patience_threshold * impatient_agent.length) := by
  constructor
  · exact totalWait_ge_of_patient patient_agent h_patient
  · exact totalWait_lt_of_impatient impatient_agent h_impatient

/-- Patience composes: a patient successor after a patient predecessor remains patient w.r.t. the earlier baseline. -/
theorem patience_compositional
    (action₁ action₂ : TimedAction)
    (h_chain : action₂.time_last_action = action₁.time_executed)
    (h₁ : is_patient action₁.time_executed action₁.time_last_action)
    (h₂ : is_patient action₂.time_executed action₂.time_last_action) :
    is_patient action₂.time_executed action₁.time_last_action := by
  unfold is_patient at *
  rw [h_chain] at h₂
  omega

/-! ### Outstanding assumptions

* `CycleAligned` will be furnished once the recognition operator scheduler exposes
  the eight-tick alignment certificate to the ethics layer.
* The periodicity hypothesis in `patience_implements_wisdom` will be derived from
  `RecognitionOperator.eight_tick_advance` when the audit bridge supplies the
  global cycle witness.  Both are tracked in the DREAM audit checklist.
-/

end Virtues
end Ethics
end IndisputableMonolith
