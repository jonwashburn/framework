import Mathlib
import IndisputableMonolith.Foundation.RecognitionOperator
import IndisputableMonolith.Ethics.MoralState
import IndisputableMonolith.Ethics.ConservationLaw
import IndisputableMonolith.Support.GoldenRatio
import IndisputableMonolith.Ethics.Virtues.Wisdom

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
  time_executed : ℕ
  time_last_action : ℕ
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
    (_h_patient : is_patient a.time_executed a.time_last_action) :
    a.time_last_action ≤ a.time_executed :=
  a.time_order

lemma time_eq_last_add_interArrival
    (a : TimedAction)
    (_h_patient : is_patient a.time_executed a.time_last_action) :
    a.time_executed = a.time_last_action + a.interArrival := by
  unfold interArrival
  have h_order := a.time_order
  omega

lemma interArrival_decompose
    (a : TimedAction)
    (h_patient : is_patient a.time_executed a.time_last_action) :
    ∃ extra : ℕ, a.interArrival = patience_threshold + extra := by
  unfold is_patient interArrival at *
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
  unfold impatiencePenalty is_patient at *
  push_neg at h_impatient
  unfold interArrival at *
  have h : min patience_threshold (a.time_executed - a.time_last_action) = a.time_executed - a.time_last_action := min_eq_right (le_of_lt h_impatient)
  rw [h]
  omega

end TimedAction

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
  obtain ⟨a, h_mem, h_imp⟩ := h_impatient
  induction actions with
  | nil => simp at h_mem
  | cons x xs ih =>
    rw [cumulativePenalty_cons]
    simp at h_mem
    cases h_mem with
    | inl h_eq =>
      subst h_eq
      have h_pos := TimedAction.impatiencePenalty_pos_of_impatient x h_imp
      omega
    | inr h_in_xs =>
      have h_exists : ∃ a' ∈ xs, ¬ is_patient a'.time_executed a'.time_last_action := ⟨a, h_in_xs, h_imp⟩
      have ih_applied := ih h_exists
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
      apply h_patient; simp
    have h_as : ∀ a' ∈ as, is_patient a'.time_executed a'.time_last_action := by
      intro a' ha'; apply h_patient; simp [ha']
    have h_ge := TimedAction.interArrival_ge_of_patient a h_a
    have ih_applied := ih h_as
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
    have h_a : ¬ is_patient a.time_executed a.time_last_action := by
      apply h_impatient; simp
    unfold is_patient at h_a
    push_neg at h_a
    by_cases h_empty : as = []
    · subst h_empty
      simp [totalWait_nil]
      unfold TimedAction.interArrival
      exact h_a
    · have ih_applied := ih (fun x hx => h_impatient x (List.mem_cons_of_mem _ hx)) h_empty
      unfold TimedAction.interArrival at *
      calc (a.time_executed - a.time_last_action) + totalWait as
          < patience_threshold + totalWait as := by omega
        _ < patience_threshold + patience_threshold * as.length := by omega
        _ = patience_threshold * (as.length + 1) := by ring

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
  by_contra h
  push_neg at h
  have h_range_sub : Finset.range patience_threshold ⊆ subset := by
    intro x hx
    exact h x hx
  have h_eq : subset = Finset.range patience_threshold := by
    exact Finset.Subset.antisymm h_subset h_range_sub
  rw [h_eq, Finset.card_range] at h_card
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
    abs (WiseChoice s choices).skew =
      abs (WiseChoice s (observationWindow stream timed_action.time_last_action)).skew := by
  have heq := wisdom_stable_under_permutation s choices (observationWindow stream timed_action.time_last_action) h_perm
  let weight := 1 / (1 + Foundation.φ)
  have h_weight_pos : 0 < weight := by
    unfold weight
    have hφ_pos : 0 < Foundation.φ := Support.GoldenRatio.phi_pos
    apply div_pos one_pos
    linarith
  -- Since weight > 0, we can cancel it from both sides.
  -- WiseChoice result scores are equal, meaning their skew natAbs are equal.
  -- wisdomScore m = |m.skew| * weight
  -- heq : |(WiseChoice s choices).skew| * weight = |(WiseChoice s obs).skew| * weight
  have h_weight_ne : weight ≠ 0 := ne_of_gt h_weight_pos
  apply mul_right_cancel₀ h_weight_ne
  simpa [wisdomScore] using heq

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
  unfold observationWindow
  rcases h_aligned with ⟨n, _, heq⟩
  rw [heq]
  apply List.ext_get
  · simp
  · intro i h1 h2
    simp only [List.get_eq_get?_get]
    have : timed_action.time_last_action + n * patience_threshold + i =
           (timed_action.time_last_action + i) + patience_threshold * n := by ring
    rw [this]
    exact periodic_shift stream h_periodic n (timed_action.time_last_action + i)

/-- Patient moral agents invest at least the cadence time per action, impatient ones do not. -/
theorem patience_long_term_thinking
    (patient_agent impatient_agent : List TimedAction)
    (h_patient : ∀ a ∈ patient_agent, is_patient a.time_executed a.time_last_action)
    (h_impatient : ∀ a ∈ impatient_agent, ¬ is_patient a.time_executed a.time_last_action) :
    patience_threshold * patient_agent.length ≤ totalWait patient_agent ∧
      (impatient_agent ≠ [] → totalWait impatient_agent < patience_threshold * impatient_agent.length) := by
  constructor
  · exact totalWait_ge_of_patient patient_agent h_patient
  · intro h_ne; exact totalWait_lt_of_impatient impatient_agent h_impatient h_ne

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

end Virtues
end Ethics
end IndisputableMonolith
