import Mathlib
import IndisputableMonolith.Ethics.MoralState
import IndisputableMonolith.Cost
import IndisputableMonolith.Foundation.RecognitionOperator

/-!
# Narrative Core: The Physics of Story

This module formalizes **Narrative** as the geometry of MoralState trajectories.

## Core Insight

Stories are not cultural artifacts — they are **geometric necessities**.
A narrative is the optimal path for consciousness to navigate from imbalance
(high σ) to balance (σ = 0).

## Key Concepts

1. **NarrativeSpace**: Manifold of MoralState trajectories
2. **PlotTension**: σ(t) — ledger skew over time
3. **NarrativeArc**: A trajectory through MoralState space
4. **StoryEnergy**: Total J-cost integrated over the arc

## Connection to RS

| RS Structure | Narrative Interpretation |
|-------------|-------------------------|
| MoralState | Point in story space |
| σ (skew) | Plot tension |
| Virtues | Allowed state transitions |
| 8-tick | Narrative rhythm/cadence |
| J-cost | "Friction" in the story |

## The Geodesic Principle

Just as:
- Light minimizes travel time → geodesics in spacetime
- Physics minimizes action → Euler-Lagrange equations

Stories minimize J-cost → **Geodesics in meaning space**

-/

namespace IndisputableMonolith
namespace Narrative

open Foundation Ethics Real

noncomputable section

/-! ## Core Definitions -/

/-- A narrative beat is a single MoralState with its context. -/
structure NarrativeBeat where
  /-- The moral state at this beat -/
  state : MoralState
  /-- Narrative time index (in 8-tick units) -/
  beat_index : ℕ
  /-- Optional semantic content (WToken-derived) -/
  semantic_tag : Option String := none

/-- A narrative arc is a finite sequence of MoralState transitions.
    This is the fundamental object of narrative physics. -/
structure NarrativeArc where
  /-- Sequence of narrative beats -/
  beats : List NarrativeBeat
  /-- The arc must be non-empty -/
  nonempty : beats ≠ []
  /-- Beats are temporally ordered -/
  ordered : ∀ i j : ℕ, i < j → (hi : i < beats.length) → (hj : j < beats.length) →
    (beats.get ⟨i, hi⟩).beat_index < (beats.get ⟨j, hj⟩).beat_index
  /-- Global admissibility is preserved (σ_total = 0 at each beat) -/
  admissible : ∀ b ∈ beats, net_skew b.state.ledger = 0

/-- Extract the underlying MoralState list from an arc -/
def NarrativeArc.states (arc : NarrativeArc) : List MoralState :=
  arc.beats.map (·.state)

/-- First beat of the arc (always exists by nonempty) -/
def NarrativeArc.initial (arc : NarrativeArc) : NarrativeBeat :=
  match h : arc.beats with
  | [] => absurd h arc.nonempty
  | b :: _ => b

/-- Alternative formulation: initial equals getElem at 0 -/
lemma NarrativeArc.initial_eq_getElem_zero (arc : NarrativeArc) :
    arc.initial = arc.beats[0]'(List.length_pos_iff_ne_nil.mpr arc.nonempty) := by
  unfold NarrativeArc.initial
  split
  · rename_i h
    exact absurd h arc.nonempty
  · rename_i b bs h
    -- Goal: b = arc.beats[0], but arc.beats = b :: bs, so arc.beats[0] = b
    simp only [h, List.getElem_cons_zero]

/-- The initial beat's skew equals the first beat's skew in the list -/
lemma NarrativeArc.initial_skew_eq (arc : NarrativeArc)
    (h : arc.beats = b :: bs) : arc.initial.state.skew = b.state.skew := by
  -- Substitute h into arc.beats in the goal
  have : arc.initial = b := by
    unfold NarrativeArc.initial
    split
    · rename_i heq
      -- heq : arc.beats = []
      rw [h] at heq
      exact absurd heq (List.cons_ne_nil b bs)
    · rename_i b' bs' heq
      -- heq : arc.beats = b' :: bs'
      -- After rw [h] at heq, we have heq : b :: bs = b' :: bs'
      rw [h] at heq
      -- From cons equality, b = b'
      have hb : b = b' := List.head_eq_of_cons_eq heq
      exact hb.symm
  rw [this]

/-- Last beat of the arc (always exists by nonempty) -/
def NarrativeArc.terminal (arc : NarrativeArc) : NarrativeBeat :=
  arc.beats.getLast arc.nonempty

/-- Duration of the arc in beat units -/
def NarrativeArc.duration (arc : NarrativeArc) : ℕ :=
  arc.terminal.beat_index - arc.initial.beat_index

/-- Number of beats in the arc -/
def NarrativeArc.length (arc : NarrativeArc) : ℕ :=
  arc.beats.length

/-! ## Arc Splicing Infrastructure -/

/-- Splice an arc by replacing beats[i..j] with alt_beats.

    Given: arc with beats = prefix ++ subarc ++ suffix
    Where: prefix = arc.beats.take i, subarc = arc.beats[i..j], suffix = arc.beats.drop(j+1)

    Returns: NarrativeArc with beats = prefix ++ alt_beats ++ suffix

    Requirements (encoded in hypotheses):
    - alt_beats is non-empty
    - The spliced list is ordered (all beat_index values strictly increase)
    - alt_beats satisfies admissibility (net_skew = 0)
-/
def NarrativeArc.splice (arc : NarrativeArc) (i j : ℕ)
    (alt_beats : List NarrativeBeat)
    (h_alt_nonempty : alt_beats ≠ [])
    (h_spliced_ordered : ∀ k₁ k₂ : ℕ, k₁ < k₂ →
      (hk1 : k₁ < (arc.beats.take i ++ alt_beats ++ arc.beats.drop (j + 1)).length) →
      (hk2 : k₂ < (arc.beats.take i ++ alt_beats ++ arc.beats.drop (j + 1)).length) →
      ((arc.beats.take i ++ alt_beats ++ arc.beats.drop (j + 1)).get ⟨k₁, hk1⟩).beat_index <
        ((arc.beats.take i ++ alt_beats ++ arc.beats.drop (j + 1)).get ⟨k₂, hk2⟩).beat_index)
    (h_alt_admissible : ∀ b ∈ alt_beats, net_skew b.state.ledger = 0) : NarrativeArc where
  beats := arc.beats.take i ++ alt_beats ++ arc.beats.drop (j + 1)

  nonempty := by
    simp only [ne_eq]
    intro h_empty
    -- If the spliced list is empty, alt_beats must be empty
    have h_len : (arc.beats.take i ++ alt_beats ++ arc.beats.drop (j + 1)).length = 0 := by
      rw [h_empty]; rfl
    simp only [List.length_append] at h_len
    have h_alt_len : alt_beats.length = 0 := by omega
    have : alt_beats = [] := List.eq_nil_of_length_eq_zero h_alt_len
    exact h_alt_nonempty this

  ordered := h_spliced_ordered

  admissible := by
    intro b hb
    simp only [List.mem_append] at hb
    cases hb with
    | inl h_prefix_or_alt =>
      cases h_prefix_or_alt with
      | inl h_in_prefix =>
        have : b ∈ arc.beats := List.mem_of_mem_take h_in_prefix
        exact arc.admissible b this
      | inr h_in_alt =>
        exact h_alt_admissible b h_in_alt
    | inr h_in_suffix =>
      have : b ∈ arc.beats := List.mem_of_mem_drop h_in_suffix
      exact arc.admissible b this

/-- The spliced arc has the expected beats. -/
lemma NarrativeArc.splice_beats (arc : NarrativeArc) (i j : ℕ)
    (alt_beats : List NarrativeBeat)
    (h_ne : alt_beats ≠ [])
    (h_ord : ∀ k₁ k₂ : ℕ, k₁ < k₂ →
      (hk1 : k₁ < (arc.beats.take i ++ alt_beats ++ arc.beats.drop (j + 1)).length) →
      (hk2 : k₂ < (arc.beats.take i ++ alt_beats ++ arc.beats.drop (j + 1)).length) →
      ((arc.beats.take i ++ alt_beats ++ arc.beats.drop (j + 1)).get ⟨k₁, hk1⟩).beat_index <
        ((arc.beats.take i ++ alt_beats ++ arc.beats.drop (j + 1)).get ⟨k₂, hk2⟩).beat_index)
    (h_adm : ∀ b ∈ alt_beats, net_skew b.state.ledger = 0) :
    (arc.splice i j alt_beats h_ne h_ord h_adm).beats =
      arc.beats.take i ++ alt_beats ++ arc.beats.drop (j + 1) := rfl

-- Helper lemmas for splice endpoint preservation

/-- When i > 0, the spliced arc has the same initial beat as the original arc. -/
lemma NarrativeArc.splice_initial_of_pos (arc : NarrativeArc) (i j : ℕ)
    (alt_beats : List NarrativeBeat)
    (h_ne : alt_beats ≠ [])
    (h_ord : ∀ k₁ k₂ : ℕ, k₁ < k₂ →
      (hk1 : k₁ < (arc.beats.take i ++ alt_beats ++ arc.beats.drop (j + 1)).length) →
      (hk2 : k₂ < (arc.beats.take i ++ alt_beats ++ arc.beats.drop (j + 1)).length) →
      ((arc.beats.take i ++ alt_beats ++ arc.beats.drop (j + 1)).get ⟨k₁, hk1⟩).beat_index <
        ((arc.beats.take i ++ alt_beats ++ arc.beats.drop (j + 1)).get ⟨k₂, hk2⟩).beat_index)
    (h_adm : ∀ b ∈ alt_beats, net_skew b.state.ledger = 0)
    (hi : 0 < i) (hi_le : i ≤ arc.length) :
    (arc.splice i j alt_beats h_ne h_ord h_adm).initial = arc.initial := by
  unfold NarrativeArc.initial NarrativeArc.splice
  simp only
  -- spliced.beats = take i ++ alt ++ drop(j+1)
  -- Since i > 0 and i ≤ arc.length, take i is nonempty
  -- (take i ++ ...).head = (take i).head = arc.beats.head = arc.initial
  have h_take_ne : arc.beats.take i ≠ [] := by
    intro h_empty
    rw [List.take_eq_nil_iff] at h_empty
    cases h_empty with
    | inl h => omega
    | inr h =>
      unfold NarrativeArc.length at hi_le
      simp only [h, List.length_nil] at hi_le
      omega
  split
  · -- Case: spliced.beats = []
    rename_i h_empty
    have : arc.beats.take i ++ alt_beats ++ arc.beats.drop (j + 1) ≠ [] := by
      intro h
      have h_len : (arc.beats.take i ++ alt_beats ++ arc.beats.drop (j + 1)).length = 0 := by
        rw [h]; rfl
      simp only [List.length_append] at h_len
      have : arc.beats.take i = [] := List.eq_nil_of_length_eq_zero (by omega)
      exact h_take_ne this
    exact absurd h_empty this
  · -- Case: spliced.beats = b :: bs
    rename_i b bs h_cons
    split
    · rename_i h_arc_empty
      exact absurd h_arc_empty arc.nonempty
    · rename_i a as h_arc_cons
      -- arc.beats = a :: as, take i (a :: as) with i > 0 gives a :: ...
      have h_take_eq : ∃ ts, arc.beats.take i = a :: ts := by
        simp only [h_arc_cons]
        use as.take (i - 1)
        have : i = (i - 1) + 1 := by omega
        conv_lhs => rw [this]
        rfl
      obtain ⟨ts, h_ts⟩ := h_take_eq
      rw [h_ts] at h_cons
      simp only [List.cons_append] at h_cons
      exact (List.head_eq_of_cons_eq h_cons).symm

/-- When j + 1 < arc.length, the spliced arc has the same terminal beat as the original arc. -/
lemma NarrativeArc.splice_terminal_of_suffix_nonempty (arc : NarrativeArc) (i j : ℕ)
    (alt_beats : List NarrativeBeat)
    (h_ne : alt_beats ≠ [])
    (h_ord : ∀ k₁ k₂ : ℕ, k₁ < k₂ →
      (hk1 : k₁ < (arc.beats.take i ++ alt_beats ++ arc.beats.drop (j + 1)).length) →
      (hk2 : k₂ < (arc.beats.take i ++ alt_beats ++ arc.beats.drop (j + 1)).length) →
      ((arc.beats.take i ++ alt_beats ++ arc.beats.drop (j + 1)).get ⟨k₁, hk1⟩).beat_index <
        ((arc.beats.take i ++ alt_beats ++ arc.beats.drop (j + 1)).get ⟨k₂, hk2⟩).beat_index)
    (h_adm : ∀ b ∈ alt_beats, net_skew b.state.ledger = 0)
    (hj : j + 1 < arc.length) :
    (arc.splice i j alt_beats h_ne h_ord h_adm).terminal = arc.terminal := by
  unfold NarrativeArc.terminal NarrativeArc.splice
  simp only
  -- spliced.beats = take i ++ alt ++ drop(j+1)
  -- Since j + 1 < arc.length, drop(j+1) is nonempty
  -- (... ++ drop(j+1)).getLast = drop(j+1).getLast = arc.beats.getLast = arc.terminal
  have h_drop_ne : arc.beats.drop (j + 1) ≠ [] := by
    simp only [ne_eq, List.drop_eq_nil_iff, not_le]
    exact hj
  rw [List.getLast_append_of_ne_nil _ h_drop_ne]
  rw [List.getLast_drop h_drop_ne]

/-- When i = 0, the spliced arc's initial is alt_beats.head -/
lemma NarrativeArc.splice_initial_of_zero (arc : NarrativeArc) (j : ℕ)
    (alt_beats : List NarrativeBeat)
    (h_ne : alt_beats ≠ [])
    (h_ord : ∀ k₁ k₂ : ℕ, k₁ < k₂ →
      (hk1 : k₁ < (arc.beats.take 0 ++ alt_beats ++ arc.beats.drop (j + 1)).length) →
      (hk2 : k₂ < (arc.beats.take 0 ++ alt_beats ++ arc.beats.drop (j + 1)).length) →
      ((arc.beats.take 0 ++ alt_beats ++ arc.beats.drop (j + 1)).get ⟨k₁, hk1⟩).beat_index <
        ((arc.beats.take 0 ++ alt_beats ++ arc.beats.drop (j + 1)).get ⟨k₂, hk2⟩).beat_index)
    (h_adm : ∀ b ∈ alt_beats, net_skew b.state.ledger = 0) :
    (arc.splice 0 j alt_beats h_ne h_ord h_adm).initial = alt_beats.head h_ne := by
  unfold NarrativeArc.initial NarrativeArc.splice
  simp only [List.take_zero, List.nil_append]
  split
  · rename_i h_empty
    have h_ne' : alt_beats ++ arc.beats.drop (j + 1) ≠ [] := by
      intro h
      have h_len : (alt_beats ++ arc.beats.drop (j + 1)).length = 0 := by rw [h]; rfl
      simp only [List.length_append] at h_len
      have : alt_beats = [] := List.eq_nil_of_length_eq_zero (by omega)
      exact h_ne this
    exact absurd h_empty h_ne'
  · rename_i b bs h_cons
    -- (alt ++ suf) = b :: bs, so b = alt.head
    have h_alt_cons : ∃ a as, alt_beats = a :: as := List.exists_cons_of_ne_nil h_ne
    obtain ⟨a, as, h_alt⟩ := h_alt_cons
    have h_eq : (a :: as) ++ arc.beats.drop (j + 1) = b :: bs := by
      rw [← h_alt]; exact h_cons
    have hb : b = a := (List.head_eq_of_cons_eq h_eq).symm
    rw [hb]
    simp only [h_alt, List.head_cons]

/-- When j + 1 ≥ arc.length (suffix empty), the spliced arc's terminal is alt_beats.getLast -/
lemma NarrativeArc.splice_terminal_of_suffix_empty (arc : NarrativeArc) (i j : ℕ)
    (alt_beats : List NarrativeBeat)
    (h_ne : alt_beats ≠ [])
    (h_ord : ∀ k₁ k₂ : ℕ, k₁ < k₂ →
      (hk1 : k₁ < (arc.beats.take i ++ alt_beats ++ arc.beats.drop (j + 1)).length) →
      (hk2 : k₂ < (arc.beats.take i ++ alt_beats ++ arc.beats.drop (j + 1)).length) →
      ((arc.beats.take i ++ alt_beats ++ arc.beats.drop (j + 1)).get ⟨k₁, hk1⟩).beat_index <
        ((arc.beats.take i ++ alt_beats ++ arc.beats.drop (j + 1)).get ⟨k₂, hk2⟩).beat_index)
    (h_adm : ∀ b ∈ alt_beats, net_skew b.state.ledger = 0)
    (hj : arc.length ≤ j + 1) :
    (arc.splice i j alt_beats h_ne h_ord h_adm).terminal = alt_beats.getLast h_ne := by
  unfold NarrativeArc.terminal NarrativeArc.splice
  simp only
  have h_drop_empty : arc.beats.drop (j + 1) = [] := by
    rw [List.drop_eq_nil_iff]
    exact hj
  simp only [h_drop_empty, List.append_nil]
  exact List.getLast_append_of_ne_nil _ h_ne

/-! ## The Narrative Space Manifold -/

/-- **NarrativeSpace** is the manifold of all narrative arcs.

    This is analogous to:
    - Phase space in classical mechanics
    - Hilbert space in quantum mechanics
    - Configuration space in field theory

    But instead of physical trajectories, we have **meaning trajectories**. -/
structure NarrativeSpace where
  /-- The current narrative arc -/
  arc : NarrativeArc
  /-- Context: what genre/mode are we in -/
  genre : String := "universal"
  /-- Narrative velocity: rate of σ change per beat -/
  tension_velocity : ℝ := 0

/-- Access all states in the narrative space -/
def NarrativeSpace.allStates (ns : NarrativeSpace) : List MoralState :=
  ns.arc.states

/-- The narrative is complete if it starts and ends with σ ≈ 0 -/
def NarrativeSpace.isComplete (ns : NarrativeSpace) : Prop :=
  |ns.arc.initial.state.skew| < 0.01 ∧ |ns.arc.terminal.state.skew| < 0.01

/-- The narrative has a crisis point if max|σ| > threshold -/
def NarrativeSpace.hasCrisis (ns : NarrativeSpace) (threshold : ℝ := 1) : Prop :=
  ∃ b ∈ ns.arc.beats, |b.state.skew| > threshold

/-! ## Story Energy: Total J-Cost of a Narrative -/

/-- Total J-cost energy of a narrative arc.
    This is the "friction" or "resistance" the story must overcome. -/
def storyEnergy (arc : NarrativeArc) : ℝ :=
  arc.beats.foldl (fun acc b =>
    acc + (b.state.ledger.active_bonds).sum (fun bond =>
      Cost.Jcost (b.state.ledger.bond_multipliers bond))) 0

/-- Story energy is always non-negative (since J ≥ 0) -/
theorem storyEnergy_nonneg (arc : NarrativeArc) : 0 ≤ storyEnergy arc := by
  unfold storyEnergy
  -- Use foldl invariant: the accumulator stays non-negative
  have h : ∀ (acc : ℝ) (bs : List NarrativeBeat), 0 ≤ acc →
      0 ≤ bs.foldl (fun acc b => acc + (b.state.ledger.active_bonds).sum
        (fun bond => Cost.Jcost (b.state.ledger.bond_multipliers bond))) acc := by
    intro acc bs hacc
    induction bs generalizing acc with
    | nil => simp [List.foldl]; exact hacc
    | cons b bs ih =>
      simp only [List.foldl_cons]
      apply ih
      apply add_nonneg hacc
      apply Finset.sum_nonneg
      intro x hx
      exact Cost.Jcost_nonneg (b.state.ledger.bond_pos hx)
  exact h 0 arc.beats (le_refl 0)

/-! ## Narrative Morphisms -/

/-- A narrative transformation is a map between narrative arcs
    that preserves the σ=0 constraint. -/
structure NarrativeMorphism where
  /-- The source arc -/
  source : NarrativeArc
  /-- The target arc -/
  target : NarrativeArc
  /-- The transformation preserves endpoints -/
  preserves_endpoints :
    source.initial.state.skew = target.initial.state.skew ∧
    source.terminal.state.skew = target.terminal.state.skew
  /-- The transformation is energy non-increasing -/
  energy_decreasing : storyEnergy target ≤ storyEnergy source

/-- Composition of narrative morphisms -/
def NarrativeMorphism.comp (f : NarrativeMorphism) (g : NarrativeMorphism)
    (h : f.target = g.source) : NarrativeMorphism where
  source := f.source
  target := g.target
  preserves_endpoints := by
    constructor
    · have h1 := f.preserves_endpoints.1
      have h2 := g.preserves_endpoints.1
      rw [h1, ← h2]
      simp only [h]
    · have h1 := f.preserves_endpoints.2
      have h2 := g.preserves_endpoints.2
      rw [h1, ← h2]
      simp only [h]
  energy_decreasing := by
    calc storyEnergy g.target ≤ storyEnergy g.source := g.energy_decreasing
      _ = storyEnergy f.target := by rw [h]
      _ ≤ storyEnergy f.source := f.energy_decreasing

/-! ## Beat-Level Structure -/

/-- Extract σ trajectory from an arc -/
def skewTrajectory (arc : NarrativeArc) : List ℝ :=
  arc.beats.map (·.state.skew)

/-- Extract energy trajectory from an arc -/
def energyTrajectory (arc : NarrativeArc) : List ℝ :=
  arc.beats.map (·.state.energy)

/-- A narrative arc respects 8-tick cadence if all beat transitions
    align with the fundamental 8-tick period. -/
def respects8TickCadence (arc : NarrativeArc) : Prop :=
  ∀ i : ℕ, (hi : i + 1 < arc.beats.length) →
    let b1 := arc.beats.get ⟨i, Nat.lt_of_succ_lt hi⟩
    let b2 := arc.beats.get ⟨i + 1, hi⟩
    (b2.beat_index - b1.beat_index) % 8 = 0 ∨
    (b2.beat_index - b1.beat_index) = 1  -- Allow sub-beat for fine structure

end

end Narrative
end IndisputableMonolith
