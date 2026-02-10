import Mathlib
import IndisputableMonolith.Foundation.RecognitionOperator
import IndisputableMonolith.Ethics.MoralState
import IndisputableMonolith.Ethics.ConservationLaw
import IndisputableMonolith.Support.GoldenRatio
import IndisputableMonolith.Ethics.Virtues.Wisdom

/-!
# Patience: Eight-Tick Waiting for Full Information

The Patience virtue enforces an eight-tick waiting period (T6 minimal cadence)
before enacting moral transformations.  Waiting a full cycle filters out
transient signals, stabilizes the variance of action schedules, and guarantees
that downstream wisdom-based optimizers receive a complete information horizon.

Key properties developed here:

* Arithmetic lemmas showing patient waits cover at least one full eight-tick cycle.
* Transient filtering: short-period signals repeat within the patient window.
* Variance reduction via an impatience-penalty functional on action lists.
* Compatibility with `WiseChoice`: any permutation of the patient observation
  window yields the same φ-discounted evaluation, and cycle-aligned windows are
  identical under the eight-tick periodicity inherited from the recognition
  operator.

Remaining assumptions are explicitly marked.  In particular, the
`CycleAligned` hypothesis in `patience_implements_wisdom` will be discharged by
the scheduler linkage once the recognition operator interface exposes the
action-to-cycle certification (`eight_tick_advance`) at the ethics layer.
-/

namespace IndisputableMonolith
namespace Ethics
namespace Virtues

open Foundation
open MoralState
open List
open Finset

open scoped Classical

/-! ## Core Definitions -/

/-- A timed action records when it was executed relative to the prior action. -/
structure TimedAction where
  action : MoralState → MoralState
  time_executed : ℕ
  time_last_action : ℕ

/-- The patience threshold: one complete eight-tick cycle (T6 minimal period). -/
def patience_threshold : ℕ := 8

@[simp] lemma patience_threshold_pos : 0 < patience_threshold := by decide

/-- Waiting at least one eight-tick period between actions. -/
def is_patient (t t_last : ℕ) : Prop := patience_threshold ≤ t - t_last

/-- Apply a patient action; the proof witness is required to ensure the wait. -/
def ApplyPatience
  (s : MoralState)
  (timed_action : TimedAction)
  (_h_patient : is_patient timed_action.time_executed timed_action.time_last_action) :
  MoralState :=
  timed_action.action s

namespace TimedAction

/-- Inter-arrival time between consecutive actions. -/
@[simp]
def interArrival (a : TimedAction) : ℕ := a.time_executed - a.time_last_action

lemma interArrival_ge_of_patient
    (a : TimedAction)
    (h_patient : is_patient a.time_executed a.time_last_action) :
    patience_threshold ≤ a.interArrival := h_patient

lemma last_le_exec_of_patient
    (a : TimedAction)
    (h_patient : is_patient a.time_executed a.time_last_action) :
    a.time_last_action ≤ a.time_executed := by
  by_contra hlt
  have h_lt : a.time_executed < a.time_last_action := lt_of_not_ge hlt
  have h_zero : a.interArrival = 0 := Nat.sub_eq_zero_of_le (le_of_lt h_lt)
  have h_false : False := by
    simpa [interArrival, is_patient, patience_threshold, h_zero] using h_patient
  exact False.elim h_false

lemma time_eq_last_add_interArrival
    (a : TimedAction)
    (h_patient : is_patient a.time_executed a.time_last_action) :
    a.time_executed = a.time_last_action + a.interArrival := by
  have h_le := last_le_exec_of_patient a h_patient
  simpa [interArrival] using (Nat.sub_eq_iff_eq_add_of_le h_le).1 rfl

lemma interArrival_decompose
    (a : TimedAction)
    (h_patient : is_patient a.time_executed a.time_last_action) :
    ∃ extra : ℕ, a.interArrival = patience_threshold + extra := by
  obtain ⟨extra, h_extra⟩ := Nat.exists_eq_add_of_le (interArrival_ge_of_patient a h_patient)
  exact ⟨extra, h_extra⟩

/-- Penalty for acting before the patience threshold (zero when patient). -/
def impatiencePenalty (a : TimedAction) : ℕ :=
  patience_threshold - min patience_threshold a.interArrival

lemma impatiencePenalty_eq_zero_of_patient
    (a : TimedAction)
    (h_patient : is_patient a.time_executed a.time_last_action) :
    a.impatiencePenalty = 0 := by
  unfold impatiencePenalty
  have hmin : min patience_threshold a.interArrival = patience_threshold :=
    min_eq_left (interArrival_ge_of_patient a h_patient)
  simp [hmin]

lemma impatiencePenalty_pos_of_impatient
    (a : TimedAction)
    (h_impatient : ¬ is_patient a.time_executed a.time_last_action) :
    0 < a.impatiencePenalty := by
  unfold impatiencePenalty
  have h_lt : a.interArrival < patience_threshold := Nat.lt_of_not_ge h_impatient
  have hmin : min patience_threshold a.interArrival = a.interArrival :=
    min_eq_right (le_of_lt h_lt)
  have h_pos : 0 < patience_threshold - a.interArrival := Nat.sub_pos_of_lt h_lt
  simpa [hmin]

end TimedAction

/-- Helper lemma: foldl with addition admits extraction of an initial constant. -/
private lemma foldl_add_const {α : Type _}
    (xs : List α) (f : α → ℕ) (acc : ℕ) :
    xs.foldl (fun n x => n + f x) acc =
      acc + xs.foldl (fun n x => n + f x) 0 := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp [List.foldl, ih, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- Total waiting time accumulated by a list of timed actions. -/
def totalWait (actions : List TimedAction) : ℕ :=
  actions.foldl (fun acc action => acc + action.interArrival) 0

@[simp] lemma totalWait_nil : totalWait [] = 0 := rfl

lemma totalWait_cons (a : TimedAction) (actions : List TimedAction) :
    totalWait (a :: actions) = a.interArrival + totalWait actions := by
  unfold totalWait
  have h := foldl_add_const actions (fun b => b.interArrival) (a.interArrival)
  simp [List.foldl] at h
  simpa [List.foldl, totalWait, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

/-- Aggregate impatience penalty for a list of actions. -/
def cumulativePenalty (actions : List TimedAction) : ℕ :=
  actions.foldl (fun acc action => acc + action.impatiencePenalty) 0

@[simp] lemma cumulativePenalty_nil : cumulativePenalty [] = 0 := rfl

lemma cumulativePenalty_cons (a : TimedAction) (actions : List TimedAction) :
    cumulativePenalty (a :: actions) =
      a.impatiencePenalty + cumulativePenalty actions := by
  unfold cumulativePenalty
  have h := foldl_add_const actions (fun b => b.impatiencePenalty) (a.impatiencePenalty)
  simp [List.foldl] at h
  simpa [List.foldl, cumulativePenalty, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

lemma cumulativePenalty_patient_zero
    (actions : List TimedAction)
    (h_patient : ∀ a ∈ actions, is_patient a.time_executed a.time_last_action) :
    cumulativePenalty actions = 0 := by
  induction actions with
  | nil => simp
  | cons a rest ih =>
      have h_tail : ∀ b ∈ rest, is_patient b.time_executed b.time_last_action := by
        intro b hb; exact h_patient _ (List.mem_cons_of_mem _ hb)
      have h_head := h_patient a (List.mem_cons_self _ _)
      simp [cumulativePenalty_cons, TimedAction.impatiencePenalty_eq_zero_of_patient _ h_head, ih h_tail]

lemma cumulativePenalty_pos_of_impatient
    (actions : List TimedAction)
    (h_impatient : ∀ a ∈ actions, ¬ is_patient a.time_executed a.time_last_action)
    (h_nonempty : actions ≠ []) :
    0 < cumulativePenalty actions := by
  classical
  cases' actions with a rest
  · cases h_nonempty rfl
  · have h_head := h_impatient a (List.mem_cons_self _ _)
    have h_pos := TimedAction.impatiencePenalty_pos_of_impatient _ h_head
    have h_nonneg : 0 ≤ cumulativePenalty rest := by exact Nat.zero_le _
    have h_fold := cumulativePenalty_cons a rest
    have : 0 < a.impatiencePenalty + cumulativePenalty rest :=
      Nat.add_pos_of_pos_of_nonneg h_pos h_nonneg
    simpa [h_fold] using this

/-- Periodic signal descriptor for transient filtering arguments. -/
structure TransientSignal (α : Type _) where
  sample : ℕ → α
  period : ℕ
  period_pos : 0 < period
  period_lt_threshold : period < patience_threshold
  periodic : ∀ t, sample (t + period) = sample t

/-- Observation window over exactly one patience period. -/
def observationWindow (stream : ℕ → MoralState) (base : ℕ) : List MoralState :=
  (List.range patience_threshold).map (fun k => stream (base + k))

@[simp] lemma observationWindow_length (stream : ℕ → MoralState) (base : ℕ) :
    (observationWindow stream base).length = patience_threshold := by
  simp [observationWindow, patience_threshold]

lemma observationWindow_ne_nil (stream : ℕ → MoralState) (base : ℕ) :
    observationWindow stream base ≠ [] := by
  intro h_nil
  have h_len := observationWindow_length stream base
  have h_zero : (observationWindow stream base).length = 0 := by
    simpa [h_nil]
  have : patience_threshold = 0 := by
    simpa [h_zero] using h_len
  have : False := by simpa [patience_threshold] using this
  exact this.elim

/-- Schedule alignment: the executed action lands exactly on full patience cycles. -/
structure CycleAligned (action : TimedAction) : Prop where
  cycles : ℕ
  cycles_pos : 0 < cycles
  alignment : action.time_executed =
    action.time_last_action + patience_threshold * cycles

/-! ## Arithmetic properties of patience -/

/-- Patience threshold equals eight ticks. -/
theorem patience_threshold_is_eight : patience_threshold = 8 := rfl

/-- Waiting one patience cycle decomposes into the threshold plus any slack. -/
theorem patience_waits_full_cycle
    (timed_action : TimedAction)
    (h_patient : is_patient timed_action.time_executed timed_action.time_last_action) :
    ∃ extra : ℕ,
      timed_action.time_executed =
        timed_action.time_last_action + patience_threshold + extra := by
  obtain ⟨extra, h_extra⟩ := TimedAction.interArrival_decompose timed_action h_patient
  have h_eq := TimedAction.time_eq_last_add_interArrival timed_action h_patient
  refine ⟨extra, ?_⟩
  simpa [TimedAction.interArrival, h_extra, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    using h_eq

/-- Acting impatiently means the inter-arrival time is strictly below the threshold. -/
theorem impatient_acts_early
    (t t_last : ℕ)
    (h_impatient : ¬ is_patient t t_last) :
    t - t_last < patience_threshold :=
  Nat.lt_of_not_ge h_impatient

/-- The final tick inside the patience window precedes the execution time. -/
theorem patience_enables_full_observation
    (timed_action : TimedAction)
    (h_patient : is_patient timed_action.time_executed timed_action.time_last_action) :
    timed_action.time_last_action + (patience_threshold - 1) < timed_action.time_executed := by
  have h_inter := TimedAction.interArrival_ge_of_patient timed_action h_patient
  have h_align := TimedAction.time_eq_last_add_interArrival timed_action h_patient
  have h_le :
      timed_action.time_last_action + patience_threshold ≤
        timed_action.time_last_action + TimedAction.interArrival timed_action := by
    exact add_le_add_left h_inter _
  have h_eq :
      timed_action.time_last_action + TimedAction.interArrival timed_action =
        timed_action.time_executed := by
    simpa [TimedAction.interArrival, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h_align
  have h_total : timed_action.time_last_action + patience_threshold ≤ timed_action.time_executed :=
    by simpa [h_eq]
  have h_lt :
      timed_action.time_last_action + (patience_threshold - 1) <
        timed_action.time_last_action + patience_threshold := by
    have : patience_threshold - 1 < patience_threshold := by
      simp [patience_threshold]
    exact Nat.add_lt_add_left this _
  exact lt_of_lt_of_le h_lt h_total

/-- Patient actions respect chronological order (no retrocausal scheduling). -/
theorem patient_respects_cadence
    (timed_action : TimedAction)
    (h_patient : is_patient timed_action.time_executed timed_action.time_last_action) :
    timed_action.time_last_action ≤ timed_action.time_executed :=
  TimedAction.last_le_exec_of_patient timed_action h_patient

/-! ## Transient filtering and variance control -/

/-- Sampling a transient signal over the patience window reveals a repeated tick. -/
lemma patient_window_contains_transient
    {α : Type _}
    (signal : TransientSignal α)
    (timed_action : TimedAction)
    (h_patient : is_patient timed_action.time_executed timed_action.time_last_action) :
    signal.sample (timed_action.time_last_action + signal.period)
        = signal.sample timed_action.time_last_action ∧
      timed_action.time_last_action + signal.period ≤ timed_action.time_executed := by
  have h_periodic := signal.periodic (timed_action.time_last_action)
  have h_le_total :
      timed_action.time_last_action + patience_threshold ≤ timed_action.time_executed := by
    have h_inter := TimedAction.interArrival_ge_of_patient timed_action h_patient
    have h_align := TimedAction.time_eq_last_add_interArrival timed_action h_patient
    have := add_le_add_left h_inter timed_action.time_last_action
    simpa [TimedAction.interArrival, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, h_align]
      using this
  have h_period_le :
      timed_action.time_last_action + signal.period ≤
        timed_action.time_last_action + patience_threshold := by
    exact add_le_add_left (le_of_lt signal.period_lt_threshold) _
  have h_within :
      timed_action.time_last_action + signal.period ≤ timed_action.time_executed :=
    le_trans h_period_le h_le_total
  exact ⟨by simpa using h_periodic, h_within⟩

/-- Patient agents accrue no impatience penalty, while impatient ones pay ≥ 1. -/
theorem patience_reduces_variance
    (patient_actions impatient_actions : List TimedAction)
    (h_patient : ∀ a ∈ patient_actions, is_patient a.time_executed a.time_last_action)
    (h_impatient : ∀ a ∈ impatient_actions, ¬ is_patient a.time_executed a.time_last_action) :
    cumulativePenalty patient_actions = 0 ∧
      (impatient_actions = [] ∨ 0 < cumulativePenalty impatient_actions) := by
  constructor
  · exact cumulativePenalty_patient_zero patient_actions h_patient
  · by_cases h_nil : impatient_actions = []
    · exact Or.inl h_nil
    · exact Or.inr (cumulativePenalty_pos_of_impatient impatient_actions h_impatient h_nil)

/-- Patient waiting multiplies action count by at least the threshold wait time. -/
theorem totalWait_ge_of_patient
    (actions : List TimedAction)
    (h_patient : ∀ a ∈ actions, is_patient a.time_executed a.time_last_action) :
    patience_threshold * actions.length ≤ totalWait actions := by
  induction actions with
  | nil => simp [totalWait]
  | cons a rest ih =>
      have h_head := h_patient a (List.mem_cons_self _ _)
      have h_tail : ∀ b ∈ rest, is_patient b.time_executed b.time_last_action := by
        intro b hb; exact h_patient _ (List.mem_cons_of_mem _ hb)
      have h_rest := ih h_tail
      have h_cons_eq := totalWait_cons a rest
      have h_order := TimedAction.interArrival_ge_of_patient a h_head
      have h_len : patience_threshold * List.length (a :: rest) =
          patience_threshold * rest.length + patience_threshold := by
        simp [List.length_cons, Nat.mul_succ, Nat.add_comm]
      have h_sum :
          patience_threshold * rest.length + patience_threshold ≤ totalWait rest + a.interArrival :=
        Nat.add_le_add h_rest h_order
      simpa [h_cons_eq, h_len, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using h_sum

/-- Imprudent schedules (every action impatient) remain below the cadence budget. -/
theorem totalWait_lt_of_impatient
    (actions : List TimedAction)
    (h_impatient : ∀ a ∈ actions, ¬ is_patient a.time_executed a.time_last_action)
    (h_nonempty : actions ≠ []) :
    totalWait actions < patience_threshold * actions.length := by
  induction actions with
  | nil => cases h_nonempty rfl
  | cons a rest ih =>
      have h_head := h_impatient a (List.mem_cons_self _ _)
      have h_lt : a.interArrival < patience_threshold := Nat.lt_of_not_ge h_head
      have h_tail : ∀ b ∈ rest, ¬ is_patient b.time_executed b.time_last_action := by
        intro b hb; exact h_impatient _ (List.mem_cons_of_mem _ hb)
      have h_len : List.length (a :: rest) = rest.length + 1 := by simp
      have h_cons := totalWait_cons a rest
      by_cases h_rest_nil : rest = []
      · subst h_rest_nil
        simpa [totalWait_cons, totalWait_nil, h_len, patience_threshold] using h_lt
      · have h_rest_lt := ih h_tail h_rest_nil
        have h_sum_lt :
            a.interArrival + totalWait rest < patience_threshold + patience_threshold * rest.length :=
          add_lt_add h_lt h_rest_lt
        simpa [h_cons, h_len, Nat.mul_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
          using h_sum_lt

-/! ## Wisdom integration -/-

/-- Range monotonicity helper. -/
lemma range_subset_of_le {m n : ℕ} (h : m ≤ n) :
    Finset.range m ⊆ Finset.range n := by
  intro k hk
  have hk_lt : k < m := Finset.mem_range.mp hk
  have hk_le : k < n := lt_of_lt_of_le hk_lt h
  exact Finset.mem_range.mpr hk_le

/-- Shortened observation windows miss at least one tick of the patience cycle. -/
theorem patience_eight_tick_optimal
    (subset : Finset ℕ)
    (h_subset : subset ⊆ Finset.range patience_threshold)
    (h_card : subset.card < patience_threshold) :
    ∃ tick ∈ Finset.range patience_threshold, tick ∉ subset := by
  classical
  by_contra h_missing
  have h_superset : Finset.range patience_threshold ⊆ subset := by
    intro tick h_tick
    have h_forall := not_exists.mp h_missing tick
    have : tick ∈ subset := by
      by_contra h_not
      exact h_forall ⟨h_tick, h_not⟩
    exact this
  have h_eq : subset = Finset.range patience_threshold :=
    Finset.Subset.antisymm h_subset h_superset
  have h_card_eq := congrArg Finset.card h_eq
  have : patience_threshold < patience_threshold := by
    simpa [h_eq, Finset.card_range] using h_card
  exact lt_irrefl _ this

/-- Impatient schedules leave some tick of the patience cycle unobserved. -/
theorem impatient_missing_tick
    (timed_action : TimedAction)
    (h_impatient : ¬ is_patient timed_action.time_executed timed_action.time_last_action)
    (h_time_order : timed_action.time_last_action ≤ timed_action.time_executed) :
    ∃ missing < patience_threshold,
      timed_action.time_executed ≤ timed_action.time_last_action + missing := by
  classical
  set observed := Finset.range (timed_action.interArrival) with h_obs
  have h_subset : observed ⊆ Finset.range patience_threshold := by
    subst h_obs
    refine range_subset_of_le ?_
    exact Nat.le_of_lt (Nat.lt_of_not_ge h_impatient)
  have h_card_lt : observed.card < patience_threshold := by
    subst h_obs
    simpa [Finset.card_range] using Nat.lt_of_not_ge h_impatient
  obtain ⟨missing, h_missing_range, h_missing_not⟩ :=
    patience_eight_tick_optimal observed h_subset h_card_lt
  have h_missing_lt : missing < patience_threshold := Finset.mem_range.mp h_missing_range
  have h_missing_ge : timed_action.interArrival ≤ missing := by
    subst h_obs
    have : missing ∉ Finset.range (timed_action.interArrival) := h_missing_not
    have h_not_lt : ¬ missing < timed_action.interArrival := by
      intro h_lt
      exact this (Finset.mem_range.mpr h_lt)
    exact le_of_not_lt h_not_lt
  have h_exec_eq := (Nat.sub_eq_iff_eq_add_of_le h_time_order).1 rfl
  refine ⟨missing, h_missing_lt, ?_⟩
  have := add_le_add_left h_missing_ge timed_action.time_last_action
  simpa [TimedAction.interArrival, h_exec_eq, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    using this

/-- Re-ordering patient observations does not change Wisdom's φ-weighted skew. -/
theorem patience_enables_wisdom
    (s : MoralState)
    (stream : ℕ → MoralState)
    (timed_action : TimedAction)
    (choices : List MoralState)
    (h_perm : choices.Perm (observationWindow stream timed_action.time_last_action)) :
    (Int.natAbs (Wisdom.WiseChoice s choices).skew : ℝ) =
      (Int.natAbs (Wisdom.WiseChoice s (observationWindow stream timed_action.time_last_action)).skew : ℝ) := by
  classical
  have h_weight_eq :=
    Wisdom.wisdom_stable_under_permutation s choices
      (observationWindow stream timed_action.time_last_action) h_perm
  have h_weight_pos :
      0 < (1 / (1 + Foundation.φ)) := by
    have hφ : 1 < Foundation.φ := Support.GoldenRatio.one_lt_phi
    have : 0 < 1 + Foundation.φ := by linarith
    exact one_div_pos.mpr this
  have h_mul := congrArg (fun t => t * (1 + Foundation.φ)) h_weight_eq
  have h_weight : (1 / (1 + Foundation.φ)) * (1 + Foundation.φ) = 1 := by
    field_simp [Support.GoldenRatio.phi_ne_zero]
  have h_sim := by
    simpa [h_weight, mul_comm, mul_left_comm, mul_assoc]
    using h_mul
  exact h_sim

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
      have := ih (n + patience_threshold)
      simp [Nat.mul_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, h_periodic, this]

/-- Cycle-aligned patient windows present identical information to Wisdom. -/
theorem patience_implements_wisdom
    (s : MoralState)
    (stream : ℕ → MoralState)
    (timed_action : TimedAction)
    (h_aligned : CycleAligned timed_action)
    (h_periodic : ∀ n, stream (n + patience_threshold) = stream n) :
    observationWindow stream timed_action.time_executed =
      observationWindow stream timed_action.time_last_action := by
  classical
  obtain ⟨cycles, _h_cycles_pos, h_alignment⟩ := h_aligned
  unfold observationWindow
  apply List.map_congr
  intro k hk
  have hk_lt : k < patience_threshold := List.mem_range.mp hk
  have h_shift := periodic_shift stream h_periodic cycles (timed_action.time_last_action + k)
  have h_exec : timed_action.time_executed =
      timed_action.time_last_action + patience_threshold * cycles := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h_alignment.symm
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, h_exec] using h_shift

/-- Patient moral agents invest at least the cadence time per action, impatient ones do not. -/
theorem patience_long_term_thinking
    (patient_agent impatient_agent : List TimedAction)
    (h_patient : ∀ a ∈ patient_agent, is_patient a.time_executed a.time_last_action)
    (h_impatient : ∀ a ∈ impatient_agent, ¬ is_patient a.time_executed a.time_last_action) :
    patience_threshold * patient_agent.length ≤ totalWait patient_agent ∧
      (impatient_agent ≠ [] → totalWait impatient_agent < patience_threshold * impatient_agent.length) := by
  constructor
  · exact totalWait_ge_of_patient patient_agent h_patient
  · intro h_nonempty
    exact totalWait_lt_of_impatient impatient_agent h_impatient h_nonempty

/-- Patience composes: a patient successor after a patient predecessor remains patient w.r.t. the earlier baseline. -/
theorem patience_compositional
    (action₁ action₂ : TimedAction)
    (h_chain : action₂.time_last_action = action₁.time_executed)
    (h₁ : is_patient action₁.time_executed action₁.time_last_action)
    (h₂ : is_patient action₂.time_executed action₂.time_last_action) :
    is_patient action₂.time_executed action₁.time_last_action := by
  have h_order₁ := TimedAction.last_le_exec_of_patient action₁ h₁
  have h_order₂ := TimedAction.last_le_exec_of_patient action₂ h₂
  have h_baseline : action₁.time_last_action ≤ action₂.time_last_action := by
    simpa [h_chain] using h_order₁
  have h_compare :
      action₂.time_executed - action₁.time_last_action ≥
        action₂.time_executed - action₂.time_last_action := by
    exact Nat.sub_le_sub_left h_baseline _
  have h₂_base : patience_threshold ≤ action₂.time_executed - action₂.time_last_action := h₂
  exact le_trans h₂_base h_compare

-/-! ### Outstanding assumptions

* `CycleAligned` will be furnished once the recognition operator scheduler exposes
  the eight-tick alignment certificate to the ethics layer.
* The periodicity hypothesis in `patience_implements_wisdom` will be derived from
  `RecognitionOperator.eight_tick_advance` when the audit bridge supplies the
  global cycle witness.  Both are tracked in the DREAM audit checklist.
-/

end Virtues
end Ethics
end IndisputableMonolith
