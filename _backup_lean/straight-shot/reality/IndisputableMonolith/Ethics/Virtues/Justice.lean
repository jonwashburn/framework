import Mathlib
import IndisputableMonolith.Foundation.RecognitionOperator
import IndisputableMonolith.Ethics.MoralState
import IndisputableMonolith.Ethics.ConservationLaw
import IndisputableMonolith.Support.GoldenRatio

namespace IndisputableMonolith
namespace Ethics
namespace Virtues

open Foundation
open MoralState

/-! ## Core Structures -/

structure Entry where
  delta : ℤ
  timestamp : ℕ
  source : AgentId
  target : AgentId

structure TimeInterval where
  ticks : ℕ

structure JusticeProtocol where
  posting : Entry → LedgerState → LedgerState
  accurate : ∀ (e : Entry) (s : LedgerState),
    net_skew s = 0 → net_skew (posting e s) = 0
  timely : ∀ (e : Entry) (s : LedgerState),
    ∃ t : TimeInterval,
      t.ticks ≤ 8 ∧
      (posting e s).time ≤ s.time + t.ticks
  sigma_preserve_balanced : ∀ (e : Entry) (s : LedgerState),
    e.delta = 0 → net_skew (posting e s) = net_skew s
  posting_compose : ∀ (e₁ e₂ : Entry) (s : LedgerState),
    posting e₂ (posting e₁ s) = posting { e₂ with delta := e₁.delta + e₂.delta } s

def ApplyJustice (protocol : JusticeProtocol) (entry : Entry) (s : MoralState) : MoralState :=
  { ledger := protocol.posting entry s.ledger
    agent_bonds := s.agent_bonds
    skew := s.skew + entry.delta
    energy := s.energy
    valid := protocol.accurate entry s.ledger s.valid
    energy_pos := s.energy_pos }

theorem justice_preserves_sigma_zero
  (protocol : JusticeProtocol)
  (entry : Entry)
  (s : MoralState)
  (h_balanced : entry.delta = 0) :
  net_skew s.ledger = 0 →
  net_skew (ApplyJustice protocol entry s).ledger = 0 := by
  intro h_sigma
  unfold ApplyJustice
  dsimp
  rw [protocol.sigma_preserve_balanced entry s.ledger h_balanced]
  assumption

theorem justice_timely
  (protocol : JusticeProtocol)
  (entry : Entry)
  (s : MoralState) :
  ∃ t : TimeInterval,
    t.ticks ≤ 8 ∧
    (ApplyJustice protocol entry s).ledger.time ≤ s.ledger.time + t.ticks := by
  obtain ⟨t, ht_bound, ht_time⟩ := protocol.timely entry s.ledger
  exact ⟨t, ht_bound, ht_time⟩

theorem justice_respects_cadence
  (protocol : JusticeProtocol)
  (entry : Entry)
  (s : MoralState) :
  (ApplyJustice protocol entry s).ledger.time - s.ledger.time ≤ 8 := by
  obtain ⟨t, ht_bound, ht_time⟩ := justice_timely protocol entry s
  omega

theorem justice_preserves_energy
  (protocol : JusticeProtocol)
  (entry : Entry)
  (s : MoralState) :
  (ApplyJustice protocol entry s).energy = s.energy := rfl

theorem justice_compositional
  (protocol : JusticeProtocol)
  (e₁ e₂ : Entry)
  (s : MoralState) :
  ApplyJustice protocol e₂ (ApplyJustice protocol e₁ s) =
  ApplyJustice protocol { e₂ with delta := e₁.delta + e₂.delta } s := by
  unfold ApplyJustice
  simp only [Int.cast_add]
  congr 1
  · exact protocol.posting_compose e₁ e₂ s.ledger
  · abel

theorem justice_local_consistency
  (protocol : JusticeProtocol)
  (entry : Entry)
  (s : MoralState) :
  (ApplyJustice protocol entry s).skew = s.skew + entry.delta := rfl

theorem justice_paired_entries
  (protocol : JusticeProtocol)
  (entry_out entry_in : Entry)
  (s : MoralState)
  (h_paired : entry_out.delta = -entry_in.delta)
  (_h_agents : entry_out.source = entry_in.target ∧ entry_out.target = entry_in.source) :
  let s₁ := ApplyJustice protocol entry_out s
  let s₂ := ApplyJustice protocol entry_in s₁
  s₂.skew = s.skew := by
  unfold ApplyJustice
  simp [h_paired]

theorem justice_enforces_accountability
  (protocol : JusticeProtocol)
  (entry : Entry)
  (s : MoralState) :
  ∃ t_max : ℕ, t_max ≤ 8 ∧
    (ApplyJustice protocol entry s).ledger.time ≤ s.ledger.time + t_max := by
  obtain ⟨t, ht_bound, ht_time⟩ := justice_timely protocol entry s
  refine ⟨t.ticks, ht_bound, ht_time⟩

theorem justice_foundational_identity (s : MoralState) :
  s = s := rfl

def simpleJusticeProtocol : JusticeProtocol where
  posting := fun _ s => s
  accurate := fun _ _ h => h
  timely := fun _ s => ⟨⟨0⟩, by decide, by simp⟩
  sigma_preserve_balanced := by
    intro e s _hδ
    simp
  posting_compose := by
    intro e₁ e₂ s
    simp

theorem simpleProtocol_is_just :
  ∀ e s, (simpleJusticeProtocol.posting e s).time ≤ s.time + 8 := by
  intro e s
  simp [simpleJusticeProtocol]

/-! ## Multi-State Justice Transitions

These theorems establish Justice preservation when operating across multiple
moral states simultaneously, which is required for the Virtue structure. -/

/-- Apply justice to each state in a list with corresponding entries -/
def ApplyJusticeToList
    (protocol : JusticeProtocol)
    (entries : List Entry)
    (states : List MoralState) : List MoralState :=
  List.zipWith (ApplyJustice protocol) entries states

/-- Total delta of a list of entries -/
def totalDelta (entries : List Entry) : ℤ :=
  (entries.map Entry.delta).sum

/-- Compute total skew delta from entries as a real number -/
def totalDeltaReal (entries : List Entry) : ℝ :=
  ((entries.map Entry.delta).sum : ℝ)

/-- Helper: foldl with accumulator shift -/
private lemma foldl_skew_shift (xs : List MoralState) (a b : ℝ) :
    List.foldl (fun x t => x + t.skew) (a + b) xs =
    List.foldl (fun x t => x + t.skew) a xs + b := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs' ih =>
    simp only [List.foldl_cons]
    -- Goal: foldl f (a + b + x.skew) xs' = foldl f (a + x.skew) xs' + b
    -- Use ih with a' = a + x.skew
    have h : a + b + x.skew = (a + x.skew) + b := by ring
    rw [h]
    exact ih (a + x.skew)

/-- Helper: foldl over zipWith adds total deltas -/
private lemma foldl_zipWith_adds_deltas
    (protocol : JusticeProtocol)
    (ents : List Entry)
    (sts : List MoralState)
    (hlen : ents.length = sts.length) :
    List.foldl (fun a t => a + t.skew) 0 (List.zipWith (ApplyJustice protocol) ents sts) =
    List.foldl (fun a t => a + t.skew) 0 sts + ((ents.map Entry.delta).sum : ℝ) := by
  induction ents generalizing sts with
  | nil =>
    cases sts with
    | nil => simp [List.zipWith]
    | cons _ _ => simp at hlen
  | cons e' es' ih =>
    cases sts with
    | nil => simp at hlen
    | cons s' ss' =>
      simp only [List.zipWith_cons_cons, List.foldl_cons, List.map_cons, List.sum_cons]
      simp only [List.length_cons] at hlen
      have hlen' : es'.length = ss'.length := by omega
      rw [foldl_skew_shift _ 0 (ApplyJustice protocol e' s').skew]
      rw [foldl_skew_shift _ 0 s'.skew]
      simp only [justice_local_consistency]
      rw [ih ss' hlen']
      simp only [Int.cast_add]
      ring

/-- When entries are balanced (sum of deltas = 0), applying justice preserves total skew -/
theorem justice_balanced_entries_preserve_total_skew
    (protocol : JusticeProtocol)
    (entries : List Entry)
    (states : List MoralState)
    (h_balanced : totalDelta entries = 0)
    (h_same_len : entries.length = states.length) :
    MoralState.total_skew (ApplyJusticeToList protocol entries states) =
    MoralState.total_skew states := by
  unfold ApplyJusticeToList MoralState.total_skew totalDelta at *
  rw [foldl_zipWith_adds_deltas protocol entries states h_same_len]
  simp only [h_balanced, Int.cast_zero, add_zero]

/-- Justice preserves global admissibility when applied with balanced entries -/
theorem justice_preserves_global_admissibility
    (protocol : JusticeProtocol)
    (entries : List Entry)
    (states : List MoralState)
    (h_admissible : MoralState.globally_admissible states)
    (h_balanced : totalDelta entries = 0)
    (h_same_len : entries.length = states.length) :
    MoralState.globally_admissible (ApplyJusticeToList protocol entries states) := by
  unfold MoralState.globally_admissible at *
  rw [justice_balanced_entries_preserve_total_skew protocol entries states h_balanced h_same_len]
  exact h_admissible

/-! ## Justice Virtue Instance

We construct a proper Virtue instance for Justice that satisfies
all the structural requirements from MoralState.lean. -/

/-- A balanced entry generator: given input states, produces entries whose deltas sum to zero -/
structure BalancedEntryGenerator where
  generate : List MoralState → List Entry
  balanced : ∀ states, totalDelta (generate states) = 0
  length_match : ∀ states, (generate states).length = states.length

/-- Helper: mapping a zero-producing function gives zero sum -/
private lemma map_zero_sum (states : List MoralState) :
    (states.map (fun s => Entry.delta ⟨0, s.time, 0, 0⟩)).sum = 0 := by
  induction states with
  | nil => simp
  | cons _ ss ih => simp only [List.map_cons, List.sum_cons, ih, add_zero]

/-- The identity entry generator (zero-delta entries) -/
def identityEntryGenerator : BalancedEntryGenerator where
  generate := fun states => states.map (fun s => ⟨0, s.time, 0, 0⟩)
  balanced := by
    intro states
    unfold totalDelta
    simp only [List.map_map, Function.comp_def]
    exact map_zero_sum states
  length_match := by
    intro states
    simp

/-- ApplyJustice preserves ledger time structure -/
theorem applyJustice_ledger_time (protocol : JusticeProtocol) (e : Entry) (s : MoralState) :
    (ApplyJustice protocol e s).ledger.time = (protocol.posting e s.ledger).time := rfl

/-- Helper: zipWith outputs have times bounded by protocol.timely -/
private lemma zipWith_time_mem_of_timely
    (protocol : JusticeProtocol)
    (entries : List Entry) (states : List MoralState) (s' : MoralState)
    (hs' : s' ∈ List.zipWith (ApplyJustice protocol) entries states) :
    ∃ s ∈ states, s'.ledger.time ≤ s.ledger.time + 8 := by
  induction entries generalizing states with
  | nil =>
    simp [List.zipWith] at hs'
  | cons e es ih =>
    cases states with
    | nil => simp [List.zipWith] at hs'
    | cons s ss =>
      simp only [List.zipWith_cons_cons, List.mem_cons] at hs'
      cases hs' with
      | inl h_eq =>
        refine ⟨s, ?_, ?_⟩
        · simp
        · rw [h_eq]
          obtain ⟨t, ht_bound, ht_time⟩ := protocol.timely e s.ledger
          simp only [applyJustice_ledger_time]
          omega
      | inr h_in_rest =>
        obtain ⟨s_orig, hs_mem, h_time⟩ := ih ss h_in_rest
        refine ⟨s_orig, ?_, h_time⟩
        simp [hs_mem]

/-- Helper: zipWith outputs with time-preserving protocol have times from original list -/
private lemma zipWith_time_preserving_mem
    (protocol : JusticeProtocol)
    (h_time_pres : ∀ e s, (protocol.posting e s).time = s.time)
    (entries : List Entry) (states : List MoralState) (s' : MoralState)
    (hs' : s' ∈ List.zipWith (ApplyJustice protocol) entries states) :
    ∃ s ∈ states, s'.ledger.time = s.ledger.time := by
  induction entries generalizing states with
  | nil =>
    simp [List.zipWith] at hs'
  | cons e es ih =>
    cases states with
    | nil => simp [List.zipWith] at hs'
    | cons s ss =>
      simp only [List.zipWith_cons_cons, List.mem_cons] at hs'
      cases hs' with
      | inl h_eq =>
        refine ⟨s, ?_, ?_⟩
        · simp
        · rw [h_eq, applyJustice_ledger_time, h_time_pres]
      | inr h_in_rest =>
        obtain ⟨s_orig, hs_mem, h_time⟩ := ih ss h_in_rest
        exact ⟨s_orig, List.mem_cons_of_mem s hs_mem, h_time⟩

/-- Construct a Justice virtue from a time-preserving protocol and balanced entry generator.
    The time-preservation assumption is required to satisfy the 8-tick cadence constraint. -/
def mkJusticeVirtue
    (protocol : JusticeProtocol)
    (h_time_pres : ∀ e s, (protocol.posting e s).time = s.time)
    (gen : BalancedEntryGenerator) : Virtue where
  transform := fun states =>
    ApplyJusticeToList protocol (gen.generate states) states

  conserves_reciprocity := by
    intro states h_admissible
    exact justice_preserves_global_admissibility protocol
      (gen.generate states) states h_admissible
      (gen.balanced states) (gen.length_match states)

  minimizes_local_J := by
    intro _states
    trivial

  respects_cadence := fun states h_coh s_in hs_in s_out hs_out => by
    -- s_out is in zipWith with time-preserving protocol
    obtain ⟨s_orig, hs_orig_mem, h_time_eq⟩ := zipWith_time_preserving_mem protocol
      h_time_pres (gen.generate states) states s_out hs_out
    -- s_out.ledger.time = s_orig.ledger.time (time preservation)
    rw [h_time_eq]
    -- Use time-coherence: s_orig.time - s_in.time ≤ 8
    have h_orig_coh := h_coh s_in hs_in s_orig hs_orig_mem
    exact h_orig_coh.1

  gauge_invariant := by
    intro _states
    trivial

/-- For simpleJusticeProtocol, ApplyJustice preserves ledger time -/
theorem simpleJustice_preserves_time (e : Entry) (s : MoralState) :
    (ApplyJustice simpleJusticeProtocol e s).ledger.time = s.ledger.time := by
  rfl

/-- Helper: elements of zipWith with simpleJusticeProtocol have times from the original list -/
private lemma zipWith_simpleJustice_time_mem
    (entries : List Entry) (states : List MoralState) (s' : MoralState)
    (hs' : s' ∈ List.zipWith (ApplyJustice simpleJusticeProtocol) entries states) :
    ∃ s ∈ states, s'.ledger.time = s.ledger.time := by
  induction entries generalizing states with
  | nil =>
    simp [List.zipWith] at hs'
  | cons e es ih =>
    cases states with
    | nil => simp [List.zipWith] at hs'
    | cons s ss =>
      simp only [List.zipWith_cons_cons, List.mem_cons] at hs'
      cases hs' with
      | inl h_eq =>
        refine ⟨s, ?_, ?_⟩
        · simp
        · rw [h_eq]; rfl
      | inr h_in_rest =>
        obtain ⟨s_orig, hs_mem, h_time⟩ := ih ss h_in_rest
        refine ⟨s_orig, ?_, h_time⟩
        simp [hs_mem]

/-- The canonical Justice virtue using the simple protocol.
    For this protocol, posting is identity so times are preserved. -/
def JusticeVirtue : Virtue where
  transform := fun states =>
    ApplyJusticeToList simpleJusticeProtocol (identityEntryGenerator.generate states) states

  conserves_reciprocity := by
    intro states h_admissible
    exact justice_preserves_global_admissibility simpleJusticeProtocol
      (identityEntryGenerator.generate states) states h_admissible
      (identityEntryGenerator.balanced states) (identityEntryGenerator.length_match states)

  minimizes_local_J := by
    intro _states
    trivial

  respects_cadence := fun states h_coh s_in hs_in s_out hs_out => by
    -- For simpleJusticeProtocol, posting is identity, so times are preserved
    -- s_out has the same time as its corresponding original state
    obtain ⟨s_orig, hs_orig_mem, h_time_eq⟩ := zipWith_simpleJustice_time_mem _ _ s_out hs_out
    -- s_out.ledger.time = s_orig.ledger.time where s_orig ∈ states
    rw [h_time_eq]
    -- Use time-coherence of input states
    have h_orig_coh := h_coh s_in hs_in s_orig hs_orig_mem
    exact h_orig_coh.1

  gauge_invariant := by
    intro _states
    trivial

/-! ## Time Coherence and Cadence

The `respects_cadence` field of `Virtue` now includes a `TimeCoherent states` precondition.
This is satisfied for states that have all their ledger times within 8 ticks of each other.

For `simpleJusticeProtocol`, times are preserved (posting is identity), so output
times equal corresponding input times. Combined with time-coherence of inputs, this
gives us the required 8-tick bound between any input and output state. -/

/-- For time-coherent inputs, JusticeVirtue respects cadence (direct application) -/
theorem justiceVirtue_respects_cadence_of_time_coherent
    (states : List MoralState)
    (h_coherent : Ethics.TimeCoherent states) :
    let states' := JusticeVirtue.transform states
    ∀ s_in ∈ states, ∀ s_out ∈ states',
      s_out.ledger.time - s_in.ledger.time ≤ 8 :=
  JusticeVirtue.respects_cadence states h_coherent

/-! ## Advanced Justice Properties -/

/-- Justice is idempotent for zero-delta entries -/
theorem justice_idempotent_zero_delta
    (protocol : JusticeProtocol)
    (e : Entry)
    (s : MoralState)
    (h_zero : e.delta = 0) :
    (ApplyJustice protocol e s).skew = s.skew := by
  simp only [justice_local_consistency, h_zero, Int.cast_zero, add_zero]

/-- Justice preserves energy under all transitions -/
theorem justice_preserves_energy_invariant
    (protocol : JusticeProtocol)
    (entries : List Entry)
    (states : List MoralState)
    (h_same_len : entries.length = states.length) :
    (ApplyJusticeToList protocol entries states).map MoralState.energy =
    states.map MoralState.energy := by
  unfold ApplyJusticeToList
  induction entries generalizing states with
  | nil =>
    cases states with
    | nil => simp [List.zipWith]
    | cons _ _ => simp at h_same_len
  | cons e es ih =>
    cases states with
    | nil => simp at h_same_len
    | cons s ss =>
      simp only [List.zipWith_cons_cons, List.map_cons]
      simp only [List.length_cons] at h_same_len
      rw [justice_preserves_energy protocol e s]
      congr 1
      exact ih ss (by omega)

/-- Justice composes correctly: sequential applications are equivalent to combined entry -/
theorem justice_sequential_composition
    (protocol : JusticeProtocol)
    (e₁ e₂ : Entry)
    (s : MoralState) :
    (ApplyJustice protocol e₂ (ApplyJustice protocol e₁ s)).skew =
    s.skew + e₁.delta + e₂.delta := by
  simp only [justice_local_consistency]
  -- Goal: (s.skew + e₁.delta) + e₂.delta = s.skew + e₁.delta + e₂.delta
  -- This is definitionally equal by associativity of addition on reals

/-- Paired entries restore original skew -/
theorem justice_paired_restores_skew
    (protocol : JusticeProtocol)
    (e : Entry)
    (s : MoralState) :
    let e_inv : Entry := { e with delta := -e.delta }
    (ApplyJustice protocol e_inv (ApplyJustice protocol e s)).skew = s.skew := by
  simp only [justice_local_consistency, Int.cast_neg]
  -- Goal: s.skew + e.delta + -e.delta = s.skew
  linarith

/-- Justice with balanced pair of entries preserves total skew for two states -/
theorem justice_pairwise_balanced
    (protocol : JusticeProtocol)
    (e₁ e₂ : Entry)
    (s₁ s₂ : MoralState)
    (h_balanced : e₁.delta + e₂.delta = 0) :
    (ApplyJustice protocol e₁ s₁).skew + (ApplyJustice protocol e₂ s₂).skew =
    s₁.skew + s₂.skew := by
  simp only [justice_local_consistency]
  have h : (e₁.delta : ℝ) + (e₂.delta : ℝ) = 0 := by
    simp only [← Int.cast_add, h_balanced, Int.cast_zero]
  linarith

/-- Total ledger validity is preserved under justice application -/
theorem justice_preserves_ledger_validity
    (protocol : JusticeProtocol)
    (entry : Entry)
    (s : MoralState) :
    net_skew (ApplyJustice protocol entry s).ledger = 0 := by
  exact (ApplyJustice protocol entry s).valid

/-! ## Transition-Specific Justice Preservation Theorems

These theorems prove Justice preservation under the specific transition types
defined in the Recognition Science framework. -/

/-- A state transition type -/
inductive StateTransition where
  | identity : StateTransition
  | posting (e : Entry) : StateTransition
  | compose (t₁ t₂ : StateTransition) : StateTransition

/-- Apply a state transition using a justice protocol -/
def applyTransition (protocol : JusticeProtocol) : StateTransition → MoralState → MoralState
  | StateTransition.identity => id
  | StateTransition.posting e => ApplyJustice protocol e
  | StateTransition.compose t₁ t₂ => fun s => applyTransition protocol t₂ (applyTransition protocol t₁ s)

/-- The net delta of a transition -/
def transitionDelta : StateTransition → ℤ
  | StateTransition.identity => 0
  | StateTransition.posting e => e.delta
  | StateTransition.compose t₁ t₂ => transitionDelta t₁ + transitionDelta t₂

/-- Justice is preserved under identity transitions -/
theorem justice_identity_preserves
    (protocol : JusticeProtocol)
    (s : MoralState) :
    applyTransition protocol StateTransition.identity s = s := rfl

/-- Justice preservation under posting transitions: net_skew is maintained -/
theorem justice_posting_preserves_net_skew
    (protocol : JusticeProtocol)
    (e : Entry)
    (s : MoralState) :
    net_skew (applyTransition protocol (StateTransition.posting e) s).ledger = 0 := by
  exact (applyTransition protocol (StateTransition.posting e) s).valid

/-- Justice preservation under composed transitions -/
theorem justice_compose_preserves_net_skew
    (protocol : JusticeProtocol)
    (t₁ t₂ : StateTransition)
    (s : MoralState) :
    net_skew (applyTransition protocol (StateTransition.compose t₁ t₂) s).ledger = 0 := by
  exact (applyTransition protocol (StateTransition.compose t₁ t₂) s).valid

/-- The skew change under a transition equals the transition delta -/
theorem justice_transition_skew_change
    (protocol : JusticeProtocol)
    (t : StateTransition)
    (s : MoralState) :
    (applyTransition protocol t s).skew = s.skew + transitionDelta t := by
  induction t generalizing s with
  | identity =>
    simp [applyTransition, transitionDelta]
  | posting e =>
    simp [applyTransition, transitionDelta, justice_local_consistency]
  | compose t₁ t₂ ih₁ ih₂ =>
    simp only [applyTransition, transitionDelta]
    rw [ih₂ (applyTransition protocol t₁ s)]
    rw [ih₁ s]
    simp only [Int.cast_add]
    ring

/-- Balanced transitions preserve total skew -/
theorem justice_balanced_transition_preserves_skew
    (protocol : JusticeProtocol)
    (t : StateTransition)
    (s : MoralState)
    (h_balanced : transitionDelta t = 0) :
    (applyTransition protocol t s).skew = s.skew := by
  rw [justice_transition_skew_change, h_balanced, Int.cast_zero, add_zero]

/-- Combined theorem: Justice is fully preserved under balanced state transitions -/
theorem justice_full_preservation
    (protocol : JusticeProtocol)
    (t : StateTransition)
    (s : MoralState)
    (h_balanced : transitionDelta t = 0) :
    -- Net skew remains zero (ledger validity)
    net_skew (applyTransition protocol t s).ledger = 0 ∧
    -- Local skew is preserved (agent balance)
    (applyTransition protocol t s).skew = s.skew ∧
    -- Energy is positive (physical viability)
    0 < (applyTransition protocol t s).energy := by
  refine ⟨?_, ?_, ?_⟩
  · exact (applyTransition protocol t s).valid
  · exact justice_balanced_transition_preserves_skew protocol t s h_balanced
  · exact (applyTransition protocol t s).energy_pos

end Virtues
end Ethics
end IndisputableMonolith
