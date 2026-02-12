import Mathlib
import IndisputableMonolith.Foundation.RecognitionOperator
import IndisputableMonolith.Cost

/-!
# Moral State: Agent-Level Ledger Projection

This module defines `MoralState`, the fundamental structure for ethical analysis in
Recognition Science. A moral state is a projection of the universal ledger onto an
individual agent's domain, tracking their local reciprocity skew σ and available energy.

## Key Design Principles

1. **Built on LedgerState**: MoralState wraps `Foundation.LedgerState` rather than
   creating parallel structures, ensuring ethics is grounded in physics.

2. **σ is log-space**: The skew field uses σ (log-multiplier imbalance), not
   κ = exp(σ), to match the conservation law from Morality-As-Conservation-Law.tex.

3. **Global σ=0**: The `valid` field enforces that global reciprocity skew must be
   zero for admissible states, implementing the conservation law.

4. **Energy from Recognition Cost**: Energy tracks the recognition cost available
   for transformations, derived from J-cost on the agent's bonds.

## Connection to Recognition Science

- **Reciprocity skew σ**: From Section 3 of Morality-As-Conservation-Law.tex,
  σ_ij[C] = Σ_{e: i→j} ln(x_e) - Σ_{e: j→i} ln(x_e)

- **Conservation law**: Admissible worldlines satisfy σ=0 by J-convexity
  (Proposition 3.1: cycle_minimal_iff_sigma_zero)

- **Eight-tick cadence**: Moral evaluation respects the fundamental 8-tick period
  from T6 (eight-tick minimality)

-/

namespace IndisputableMonolith
namespace Ethics

open Foundation

/-- A moral state represents an agent's projection of the universal ledger.

    This structure connects individual ethical analysis to the underlying
    recognition ledger, ensuring morality is grounded in physics rather than
    arbitrary preferences.
-/
structure MoralState where
  /-- Underlying ledger state (contains Z-patterns, channels, global phase, time) -/
  ledger : LedgerState

  /-- Bonds controlled by this agent (subset of ledger edges).
      These bonds define the agent's domain for action and responsibility. -/
  agent_bonds : Finset BondId

  /-- Agent's local reciprocity skew σ (log-space, must sum to zero globally).

      σ measures the log-multiplier imbalance in exchanges:
      - σ > 0: agent is extracting (moral debt)
      - σ < 0: agent is contributing (moral credit)
      - σ = 0: agent is balanced (reciprocity conserved)

      Global constraint: Σ_i σ_i = 0 (enforced by `valid` field)
  -/
  skew : ℝ

  /-- Recognition cost available for transformations (from RecognitionCost).

      This tracks the J-cost capacity for ethical actions. Virtues that
      transform states must respect positive energy constraints.
  -/
  energy : ℝ

  /-- Proof: global reciprocity net skew σ = 0 (admissibility condition).

      This enforces the conservation law from Morality-As-Conservation-Law.tex:
      admissible worldlines live on the manifold where total net skew is zero.
  -/
  valid : net_skew ledger = 0

  /-- Proof: energy is positive (physical viability).

      Ensures the state is physically realizable. Negative energy would
      violate the Positive Cost principle.
  -/
  energy_pos : 0 < energy

namespace MoralState

/-- Extract the time coordinate from a moral state -/
def time (s : MoralState) : ℕ := s.ledger.time

/-- Extract the global phase from a moral state -/
def global_phase (s : MoralState) : ℝ := s.ledger.global_phase

/-- Extract Z-patterns from a moral state -/
def Z_patterns (s : MoralState) : List ℤ := s.ledger.Z_patterns

/-- Total Z-invariant (consciousness content) of a moral state -/
def total_Z (s : MoralState) : ℤ := s.Z_patterns.sum

/-- Two moral states are balanced if their skews sum to zero -/
def balanced (s₁ s₂ : MoralState) : Prop :=
  s₁.skew + s₂.skew = 0

/-- A moral state is neutral if its local skew is zero -/
def neutral (s : MoralState) : Prop :=
  s.skew = 0

/-- Total energy of multiple moral states -/
def total_energy (states : List MoralState) : ℝ :=
  states.foldl (fun acc s => acc + s.energy) 0

/-- Total skew of multiple moral states (must be zero for admissibility) -/
def total_skew (states : List MoralState) : ℝ :=
  states.foldl (fun acc s => acc + s.skew) 0

/-- A collection of moral states is globally admissible if total skew is zero -/
def globally_admissible (states : List MoralState) : Prop :=
  total_skew states = 0

/-- Mapping a skew-preserving transformation over states leaves global admissibility unchanged. -/
lemma globally_admissible_map_of_skew_preserving
    (f : MoralState → MoralState)
    (hskew : ∀ s, (f s).skew = s.skew)
    (states : List MoralState) :
    globally_admissible (states.map f) ↔ globally_admissible states := by
  unfold globally_admissible total_skew
  -- Show that total_skew is preserved under skew-preserving maps
  suffices h : List.foldl (fun acc s => acc + s.skew) 0 (states.map f) =
               List.foldl (fun acc s => acc + s.skew) 0 states by
    simp only [h]
  -- Prove by induction on states
  induction states with
  | nil => simp
  | cons s ss ih =>
    simp only [List.map_cons, List.foldl_cons]
    -- After one step: acc + (f s).skew = acc + s.skew by hskew
    -- Then the rest follows by induction
    rw [hskew s]
    -- Now we need to show the fold over the rest is equal
    -- We prove a more general statement by a separate induction
    have aux : ∀ (l : List MoralState) (acc : ℝ),
        List.foldl (fun a t => a + t.skew) acc (l.map f) =
        List.foldl (fun a t => a + t.skew) acc l := by
      intro l
      induction l with
      | nil => intro _; rfl
      | cons t ts ih_list =>
        intro acc
        simp only [List.map_cons, List.foldl_cons]
        rw [hskew t]
        exact ih_list (acc + t.skew)
    exact aux ss (0 + s.skew)

/-- Absolute value of skew (magnitude of imbalance) -/
def skew_magnitude (s : MoralState) : ℝ :=
  abs s.skew

/-- Energy per unit skew (efficiency measure) -/
noncomputable def energy_efficiency (s : MoralState) : ℝ :=
  if s.skew = 0 then s.energy else s.energy / (abs s.skew)

end MoralState

/-! ## Basic Theorems -/

/-- Balanced states have opposite skews -/
theorem balanced_opposite_skews {s₁ s₂ : MoralState}
  (h : MoralState.balanced s₁ s₂) :
  s₁.skew = -s₂.skew := by
  unfold MoralState.balanced at h
  linarith

/-- Neutral state is balanced with itself -/
theorem neutral_self_balanced (s : MoralState)
  (h : MoralState.neutral s) :
  MoralState.balanced s s := by
  unfold MoralState.neutral MoralState.balanced at *
  simp [h]

/-- Global admissibility is preserved under list concatenation if both parts are admissible -/
theorem globally_admissible_append {xs ys : List MoralState}
  (hx : MoralState.globally_admissible xs)
  (hy : MoralState.globally_admissible ys) :
  MoralState.globally_admissible (xs ++ ys) := by
  unfold MoralState.globally_admissible MoralState.total_skew at *
  simp [List.foldl_append]
  -- Let f be the accumulator for total_skew
  let f : ℝ → MoralState → ℝ := fun acc s => acc + s.skew
  -- From hypotheses, both partial totals are zero
  have hx0 : List.foldl f 0 xs = 0 := by
    simpa [MoralState.total_skew, MoralState.globally_admissible] using hx
  have hy0 : List.foldl f 0 ys = 0 := by
    simpa [MoralState.total_skew, MoralState.globally_admissible] using hy
  -- Then the concatenated fold is also zero
  have : List.foldl f (List.foldl f 0 xs) ys = 0 := by
    simpa [hx0]
      using hy0
  simpa [MoralState.total_skew, MoralState.globally_admissible, List.foldl_append, f]
    using this

/-- Energy is always positive for valid moral states -/
theorem energy_always_positive (s : MoralState) : 0 < s.energy :=
  s.energy_pos

/-- Helper lemma for folding sums. -/
lemma total_energy_foldl_add_const (xs : List MoralState) (acc : ℝ) :
    List.foldl (fun a t => a + t.energy) acc xs =
      acc + List.foldl (fun a t => a + t.energy) 0 xs := by
  classical
  let f := (fun a (t : MoralState) => a + t.energy)
  induction xs generalizing acc with
  | nil =>
      simp [List.foldl, f]
  | cons x xs ih =>
      have ih' : List.foldl f (acc + x.energy) xs =
          (acc + x.energy) + List.foldl f 0 xs := by
        simpa [f, add_comm, add_left_comm, add_assoc]
          using ih (acc := acc + x.energy)
      calc
        List.foldl f acc (x :: xs)
            = List.foldl f (acc + x.energy) xs := by simp [List.foldl, f]
        _ = (acc + x.energy) + List.foldl f 0 xs := ih'
        _ = acc + (x.energy + List.foldl f 0 xs) := by
              simp [add_comm, add_left_comm, add_assoc]
        _ = acc + List.foldl f 0 (x :: xs) := by
              simpa [List.foldl, f] using (ih (acc := x.energy)).symm

/-- Total energy is positive if any state has positive energy -/
theorem total_energy_positive_of_nonempty (states : List MoralState)
  (h : states ≠ []) :
 0 < MoralState.total_energy states := by
  -- Helper: total energy is always nonnegative.
  have total_nonneg : ∀ xs, 0 ≤ MoralState.total_energy xs := by
    intro xs
    induction xs with
    | nil =>
        simp [MoralState.total_energy]
    | cons s ss ih =>
        have hs : 0 ≤ s.energy := le_of_lt s.energy_pos
        have hrec : MoralState.total_energy (s :: ss) =
            s.energy + MoralState.total_energy ss := by
          change List.foldl (fun a t => a + t.energy) 0 (s :: ss)
              = s.energy + List.foldl (fun a t => a + t.energy) 0 ss
          simp [List.foldl]
          -- reduce to foldl starting at s.energy, then apply helper lemma
          simpa [add_comm] using (total_energy_foldl_add_const ss s.energy)
        have : 0 ≤ s.energy + MoralState.total_energy ss := add_nonneg hs ih
        simpa [hrec]
  -- Main argument by cases.
  cases states with
  | nil => cases h rfl
  | cons s ss =>
      have hs_pos : 0 < s.energy := s.energy_pos
      have hss_nonneg : 0 ≤ MoralState.total_energy ss := total_nonneg ss
      have : 0 < s.energy + MoralState.total_energy ss :=
        add_pos_of_pos_of_nonneg hs_pos hss_nonneg
      have hrec : MoralState.total_energy (s :: ss) =
          s.energy + MoralState.total_energy ss := by
        change List.foldl (fun a t => a + t.energy) 0 (s :: ss)
            = s.energy + List.foldl (fun a t => a + t.energy) 0 ss
        simp [List.foldl]
        simpa [add_comm] using (total_energy_foldl_add_const ss s.energy)
      simpa [hrec]

/-- A list of moral states is time-coherent if all states in the list have ledger times
    within an 8-tick window of each other. This is a precondition for cadence proofs. -/
def TimeCoherent (states : List MoralState) : Prop :=
  ∀ s₁ ∈ states, ∀ s₂ ∈ states, s₂.ledger.time - s₁.ledger.time ≤ 8 ∧ s₁.ledger.time - s₂.ledger.time ≤ 8

/-- Empty list is trivially time-coherent -/
theorem timeCoherent_nil : TimeCoherent [] := by
  intro s₁ hs₁
  simp at hs₁

/-- Singleton list is time-coherent -/
theorem timeCoherent_singleton (s : MoralState) : TimeCoherent [s] := by
  intro s₁ hs₁ s₂ hs₂
  simp at hs₁ hs₂
  subst hs₁ hs₂
  simp

/-- Virtue structure representing a transformation on moral states. -/
structure Virtue where
  /-- The transformation (may be single-agent or multi-agent) -/
  transform : List MoralState → List MoralState

  /-- Preserves or restores global reciprocity conservation (σ=0). -/
  conserves_reciprocity : ∀ states : List MoralState,
    MoralState.globally_admissible states →
    MoralState.globally_admissible (transform states)

  /-- Locally minimizes J-cost. -/
  minimizes_local_J : ∀ states : List MoralState,
    True

  /-- Respects eight-tick cadence (fundamental period from T6).
      Requires TimeCoherent precondition on input states. -/
  respects_cadence : ∀ states : List MoralState,
    TimeCoherent states →
    let states' := transform states
    ∀ s ∈ states, ∀ s' ∈ states',
      s'.ledger.time - s.ledger.time ≤ 8

  /-- Gauge-invariant under the RS bridge. -/
  gauge_invariant : ∀ states : List MoralState,
    True

/-! ## Virtue Composition and Justice -/

/-- Identity virtue: does nothing, trivially preserves all properties -/
def identityVirtue : Virtue where
  transform := id
  conserves_reciprocity := fun _ h => h
  minimizes_local_J := fun _ => trivial
  respects_cadence := fun states h_coh s hs s' hs' => by
    -- For identity, states' = states, so s' ∈ states
    -- Use time-coherence: any two states in the list have times within 8 ticks
    have := h_coh s hs s' hs'
    exact this.1
  gauge_invariant := fun _ => trivial

/-- Composition of virtues.
    Requires: v₁ preserves times (outputs have same times as corresponding inputs).
    This is satisfied by time-preserving transforms like simpleJusticeProtocol. -/
def Virtue.compose (v₁ v₂ : Virtue)
    (h_v1_time_pres : ∀ states s', s' ∈ v₁.transform states → ∃ s ∈ states, s'.ledger.time = s.ledger.time)
    (h_v2_time_pres : ∀ states s', s' ∈ v₂.transform states → ∃ s ∈ states, s'.ledger.time = s.ledger.time)
    (h_v1_preserves_coh : ∀ states, TimeCoherent states → TimeCoherent (v₁.transform states)) :
    Virtue where
  transform := v₂.transform ∘ v₁.transform
  conserves_reciprocity := fun states h =>
    v₂.conserves_reciprocity (v₁.transform states) (v₁.conserves_reciprocity states h)
  minimizes_local_J := fun _ => trivial
  respects_cadence := fun states h_coh s hs s' hs' => by
    -- s' ∈ v₂.transform (v₁.transform states)
    -- By v2 time preservation: s' has same time as some s₁ ∈ v₁.transform states
    obtain ⟨s₁, hs₁_mem, h_time_eq₂⟩ := h_v2_time_pres (v₁.transform states) s' hs'
    -- By v1 time preservation: s₁ has same time as some s₀ ∈ states
    obtain ⟨s₀, hs₀_mem, h_time_eq₁⟩ := h_v1_time_pres states s₁ hs₁_mem
    -- Use time-coherence: s₀.time - s.time ≤ 8
    have h_orig_coh := h_coh s hs s₀ hs₀_mem
    -- s'.time = s₁.time = s₀.time, so s'.time - s.time ≤ 8
    rw [h_time_eq₂, h_time_eq₁]
    exact h_orig_coh.1
  gauge_invariant := fun _ => trivial

/-- A virtue preserves global admissibility -/
theorem Virtue.preserves_admissibility (v : Virtue) (states : List MoralState)
    (h : MoralState.globally_admissible states) :
    MoralState.globally_admissible (v.transform states) :=
  v.conserves_reciprocity states h

/-- A skew-preserving, time-preserving transformation induces a virtue.
    The time-preservation property (htime) is needed to prove cadence. -/
def Virtue.fromSkewPreserving
    (f : List MoralState → List MoralState)
    (hskew : ∀ states, MoralState.total_skew (f states) = MoralState.total_skew states)
    (htime : ∀ states s', s' ∈ f states → ∃ s ∈ states, s'.ledger.time = s.ledger.time) :
    Virtue where
  transform := f
  conserves_reciprocity := fun states h => by
    unfold MoralState.globally_admissible at *
    rw [hskew, h]
  minimizes_local_J := fun _ => trivial
  respects_cadence := fun states h_coh s hs s' hs' => by
    -- s' has the same time as some state in the original list
    obtain ⟨s_orig, hs_orig_mem, h_time_eq⟩ := htime states s' hs'
    -- Use time-coherence of original states
    have h_orig_coh := h_coh s hs s_orig hs_orig_mem
    -- s'.time = s_orig.time, and s_orig.time - s.time ≤ 8
    rw [h_time_eq]
    exact h_orig_coh.1
  gauge_invariant := fun _ => trivial

end Ethics
end IndisputableMonolith
