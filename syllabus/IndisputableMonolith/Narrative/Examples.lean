import Mathlib
import IndisputableMonolith.Narrative.Core
import IndisputableMonolith.Narrative.PlotTension
import IndisputableMonolith.Narrative.FundamentalPlots
import IndisputableMonolith.Narrative.StoryGeodesic

/-!
# Narrative Examples: Concrete Story Instances

This module provides concrete examples of narrative arcs, demonstrating
how the Physics of Narrative applies to actual stories.

## Purpose

1. Validate the formalism against intuition
2. Provide test cases for the theory
3. Illustrate the 7 fundamental plot types
4. Show how geodesic structure emerges

## Proof Status

The structural proofs (ordering, admissibility) are fully verified.
Classification theorems are marked as HYPOTHESIS because `classifyPlot`
involves noncomputable Real arithmetic that cannot be evaluated by `decide`.

-/

namespace IndisputableMonolith
namespace Narrative
namespace Examples

open Foundation Ethics Real

noncomputable section

/-! ## Helper: Construct a NarrativeBeat from skew and energy -/

/-- Create a placeholder MoralState for examples -/
private def mkPlaceholderLedger : LedgerState := {
  channels := fun _ => 0
  Z_patterns := []
  global_phase := 0
  time := 0
  active_bonds := ∅
  bond_multipliers := fun _ => 1
  bond_pos := fun h => absurd h (Finset.notMem_empty _)
  bond_agents := fun _ => none
}

/-- Placeholder proof for ledger validity -/
private lemma placeholder_valid : net_skew mkPlaceholderLedger = 0 := by
  unfold net_skew mkPlaceholderLedger
  simp [Finset.sum_empty]

/-- Create a MoralState with given skew and energy -/
private def mkMoralState (σ : ℝ) (E : ℝ) (hE : 0 < E := by norm_num) : MoralState := {
  ledger := mkPlaceholderLedger
  agent_bonds := ∅
  skew := σ
  energy := E
  valid := placeholder_valid
  energy_pos := hE
}

/-- Create a NarrativeBeat from skew, energy, and beat index -/
def mkBeat (σ : ℝ) (E : ℝ) (idx : ℕ) (hE : 0 < E := by norm_num) : NarrativeBeat := {
  state := mkMoralState σ E hE
  beat_index := idx
  semantic_tag := none
}

/-! ## Example 1: The Hero's Journey (Overcoming the Monster) -/

/-- The Hero's Journey σ-trajectory:
    0 → 0.5 → 1.0 → 1.4 → 1.8 → 0.9 → 0.4 → 0

    Eight beats representing:
    1. Ordinary world (σ = 0)
    2. Call to adventure (σ = 0.5)
    3. Crossing threshold (σ = 1.0)
    4. Rising action (σ = 1.4)
    5. Ordeal/climax (σ = 1.8) ← climax at index 4 (4/8 = 0.5 ≥ 0.4 → OvercomingMonster)
    6. Road back (σ = 0.9)
    7. Resurrection (σ = 0.4)
    8. Return (σ = 0)

    Note: Climax at position 0.5 (≥ 0.4) classifies as OvercomingMonster.
    VoyageAndReturn would have peak_early (< 0.4). -/
def herosJourneyBeats : List NarrativeBeat := [
  mkBeat 0.0 1.0 0,
  mkBeat 0.5 1.2 8,
  mkBeat 1.0 1.5 16,
  mkBeat 1.4 1.7 24,  -- Rising action
  mkBeat 1.8 2.0 32,  -- Climax: σ = 1.8 > φ ≈ 1.618, at index 4
  mkBeat 0.9 1.4 40,
  mkBeat 0.4 1.1 48,
  mkBeat 0.0 1.0 56
]

/-- Helper: beat indices are strictly increasing -/
private lemma herosJourneyBeats_ordered (i j : ℕ) (hij : i < j)
    (hi : i < herosJourneyBeats.length) (hj : j < herosJourneyBeats.length) :
    (herosJourneyBeats.get ⟨i, hi⟩).beat_index < (herosJourneyBeats.get ⟨j, hj⟩).beat_index := by
  simp only [herosJourneyBeats, List.length_cons, List.length_nil] at hi hj
  -- Beat indices are [0, 8, 16, 24, 32, 40, 48, 56]
  interval_cases i <;> interval_cases j <;> simp_all [herosJourneyBeats, mkBeat]

/-- Helper: all beats have zero net skew -/
private lemma herosJourneyBeats_admissible (b : NarrativeBeat) (hb : b ∈ herosJourneyBeats) :
    net_skew b.state.ledger = 0 := by
  -- All beats are constructed with mkPlaceholderLedger which has net_skew = 0
  simp only [herosJourneyBeats, List.mem_cons, List.mem_nil_iff, or_false] at hb
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl := hb
  all_goals exact placeholder_valid

/-- The Hero's Journey as a NarrativeArc -/
def herosJourney : NarrativeArc := {
  beats := herosJourneyBeats
  nonempty := List.cons_ne_nil _ _
  ordered := herosJourneyBeats_ordered
  admissible := herosJourneyBeats_admissible
}

/-- **THEOREM**: The Hero's Journey has the "Overcoming the Monster" plot type.
    Classification based on σ-trajectory: [0, 0.5, 1.0, 1.4, 1.8, 0.9, 0.4, 0]
    Peak at index 4 (position 0.5 ≥ 0.4), then decreasing → OvercomingMonster pattern.

    **Proof sketch**: For classifyPlot to return OvercomingMonster:
    1. has_peak ∧ starts_low ∧ ends_low must be true
    2. peak_early must be false (climax_position ≥ 0.4)

    For herosJourney:
    - initial tension = 0 < 1/φ ≈ 0.618 → starts_low = true
    - final tension = 0 < 1/φ ≈ 0.618 → ends_low = true
    - peak tension = 1.8 > φ ≈ 1.618 → has_peak = true
    - climax_position = 4/8 = 0.5 ≥ 0.4 → peak_early = false

    **Note**: Proof blocked by need to unfold noncomputable Real list operations.
    Verified by inspection of concrete values. -/
-- Helper lemmas for hero's journey classification
private lemma herosJourney_initial_tension : plotTension herosJourney.initial = 0 := by
  unfold plotTension herosJourney NarrativeArc.initial herosJourneyBeats mkBeat mkMoralState
  norm_num

private lemma herosJourney_final_tension : plotTension herosJourney.terminal = 0 := by
  unfold plotTension herosJourney NarrativeArc.terminal herosJourneyBeats mkBeat mkMoralState
  norm_num

private lemma herosJourney_initial_lt_threshold :
    plotTension herosJourney.initial < lowTensionThreshold := by
  rw [herosJourney_initial_tension, lowTensionThreshold]
  exact div_pos one_pos Constants.phi_pos

private lemma herosJourney_final_lt_threshold :
    plotTension herosJourney.terminal < lowTensionThreshold := by
  rw [herosJourney_final_tension, lowTensionThreshold]
  exact div_pos one_pos Constants.phi_pos

-- Helper: tensions list for hero's journey
private lemma herosJourney_tensions :
    tensionTrajectory herosJourney = [0, 0.5, 1, 1.4, 1.8, 0.9, 0.4, 0] := by
  unfold tensionTrajectory herosJourney herosJourneyBeats plotTension mkBeat mkMoralState
  simp only [List.map]
  norm_num

-- Helper: peak tension of hero's journey is 1.8
private lemma herosJourney_peak_tension : (tensionProfile herosJourney).peak = 1.8 := by
  unfold tensionProfile accumulateTension
  simp only [herosJourney, herosJourneyBeats]
  -- The peak is the max of all tensions
  -- We need to show foldl TensionAccumulator.addBeat empty [b0,..,b7] has peak = 1.8
  -- The tensions are [0, 0.5, 1, 1.4, 1.8, 0.9, 0.4, 0]
  -- max of these is 1.8
  simp only [List.foldl, TensionAccumulator.addBeat, TensionAccumulator.empty]
  simp only [plotTension, mkBeat, mkMoralState]
  norm_num [max_def, abs_of_nonneg, abs_of_pos, abs_of_neg]

-- Helper: maxTension of hero's journey is 1.8
private lemma herosJourney_maxTension : maxTension herosJourney = 1.8 := by
  unfold maxTension tensionTrajectory herosJourney herosJourneyBeats plotTension mkBeat mkMoralState
  simp only [List.map, List.foldl]
  norm_num [max_def]

/-- **THEOREM**: The Hero's Journey climax is at beat 4 (index 4).
    The σ-trajectory is [0.0, 0.5, 1.0, 1.4, 1.8, 0.9, 0.4, 0.0].
    maxTension = 1.8 at index 4. -/
theorem H_herosJourney_climax_position : climaxIndex herosJourney = 4 := by
  unfold climaxIndex
  rw [herosJourney_tensions, herosJourney_maxTension]
  -- Goal: [0, 0.5, 1, 1.4, 1.8, 0.9, 0.4, 0].findIdx (· = 1.8) = 4
  -- Prove non-equalities
  have h0 : (0 : ℝ) ≠ 1.8 := by norm_num
  have h1 : (0.5 : ℝ) ≠ 1.8 := by norm_num
  have h2 : (1 : ℝ) ≠ 1.8 := by norm_num
  have h3 : (1.4 : ℝ) ≠ 1.8 := by norm_num
  have h4 : (1.8 : ℝ) = 1.8 := rfl
  -- Convert to decide = false/true
  have d0 : decide ((0 : ℝ) = 1.8) = false := decide_eq_false h0
  have d1 : decide ((0.5 : ℝ) = 1.8) = false := decide_eq_false h1
  have d2 : decide ((1 : ℝ) = 1.8) = false := decide_eq_false h2
  have d3 : decide ((1.4 : ℝ) = 1.8) = false := decide_eq_false h3
  have d4 : decide ((1.8 : ℝ) = 1.8) = true := decide_eq_true h4
  -- Unfold findIdx step by step and simplify bif
  -- d4 tells us decide True = true, so bif decide True reduces to first branch
  simp only [List.findIdx, List.findIdx.go, d0, d1, d2, d3, d4, cond_false, cond_true]
  norm_num

-- Helper: climax position is 0.5 (index 4 out of 8)
-- Proved using climaxIndex = 4 and length = 8
private lemma herosJourney_climax_pos : (tensionProfile herosJourney).climax_position = 0.5 := by
  have h_len : herosJourney.length = 8 := by
    unfold NarrativeArc.length herosJourney herosJourneyBeats
    simp only [List.length_cons, List.length_nil]
  have h_climax : climaxIndex herosJourney = 4 := H_herosJourney_climax_position
  unfold tensionProfile
  simp only [h_len, h_climax]
  norm_num

theorem H_herosJourney_is_overcoming : classifyPlot herosJourney = .OvercomingMonster := by
  unfold classifyPlot
  -- Key facts about the tension profile
  have h_starts_low : (tensionProfile herosJourney).initial < lowTensionThreshold := by
    unfold tensionProfile lowTensionThreshold
    rw [herosJourney_initial_tension]
    exact div_pos one_pos Constants.phi_pos
  have h_ends_low : (tensionProfile herosJourney).final < lowTensionThreshold := by
    unfold tensionProfile lowTensionThreshold
    rw [herosJourney_final_tension]
    exact div_pos one_pos Constants.phi_pos
  have h_has_peak : (tensionProfile herosJourney).peak > highTensionThreshold := by
    rw [herosJourney_peak_tension, highTensionThreshold]
    have := Constants.phi_lt_onePointSixTwo
    linarith
  have h_not_peak_early : ¬((tensionProfile herosJourney).climax_position < 0.4) := by
    rw [herosJourney_climax_pos]
    norm_num
  -- Now the if-then-else reduces
  simp only [lowTensionThreshold, highTensionThreshold] at *
  simp only [h_starts_low, h_ends_low, h_has_peak, h_not_peak_early, and_true, ↓reduceIte,
    decide_eq_true_eq]

-- Backward-compatible aliases
abbrev herosJourney_is_overcoming := H_herosJourney_is_overcoming
abbrev herosJourney_climax_position := H_herosJourney_climax_position

/-! ## Example 2: Tragedy (Macbeth-style) -/

/-- Tragedy σ-trajectory:
    0 → 0.3 → 0.7 → 1.2 → 1.8 → 2.5

    Monotonically increasing tension with no resolution -/
def tragedyBeats : List NarrativeBeat := [
  mkBeat 0.0 1.0 0,
  mkBeat 0.3 1.1 8,
  mkBeat 0.7 1.3 16,
  mkBeat 1.2 1.5 24,
  mkBeat 1.8 1.8 32,
  mkBeat 2.5 2.0 40
]

/-- Helper: tragedy beat indices are strictly increasing -/
private lemma tragedyBeats_ordered (i j : ℕ) (hij : i < j)
    (hi : i < tragedyBeats.length) (hj : j < tragedyBeats.length) :
    (tragedyBeats.get ⟨i, hi⟩).beat_index < (tragedyBeats.get ⟨j, hj⟩).beat_index := by
  simp only [tragedyBeats, List.length_cons, List.length_nil] at hi hj
  interval_cases i <;> interval_cases j <;> simp_all [tragedyBeats, mkBeat]

/-- Helper: all tragedy beats have zero net skew -/
private lemma tragedyBeats_admissible (b : NarrativeBeat) (hb : b ∈ tragedyBeats) :
    net_skew b.state.ledger = 0 := by
  simp only [tragedyBeats, List.mem_cons, List.mem_nil_iff, or_false] at hb
  obtain rfl | rfl | rfl | rfl | rfl | rfl := hb
  all_goals exact placeholder_valid

/-- Tragedy arc -/
def tragedy : NarrativeArc := {
  beats := tragedyBeats
  nonempty := List.cons_ne_nil _ _
  ordered := tragedyBeats_ordered
  admissible := tragedyBeats_admissible
}

-- Helper lemmas for tragedy classification
private lemma tragedy_initial_tension : plotTension tragedy.initial = 0 := by
  unfold plotTension tragedy NarrativeArc.initial tragedyBeats mkBeat mkMoralState
  norm_num

private lemma tragedy_final_tension : plotTension tragedy.terminal = 2.5 := by
  unfold plotTension tragedy NarrativeArc.terminal tragedyBeats mkBeat mkMoralState
  norm_num

/-- **THEOREM**: Tragedy is classified correctly.
    Monotonically increasing σ with no resolution → Tragedy.

    **Proof sketch**: classifyPlot checks:
    - starts_low: initial = |0| = 0 < 1/φ ✓ (0 < 0.618)
    - ends_low: final = |2.5| = 2.5 > 1/φ, so ends_low = false
    - `starts_low ∧ ¬ends_low` → Tragedy

    Verified by concrete calculation. -/
theorem H_tragedy_is_tragedy : classifyPlot tragedy = .Tragedy := by
  unfold classifyPlot
  -- Key facts about thresholds
  have h_phi_pos : Constants.phi > 0 := Constants.phi_pos
  have h_inv_pos : 0 < 1 / Constants.phi := div_pos one_pos h_phi_pos
  have h_phi_lt_2 : Constants.phi < 2 := by
    have := Constants.phi_lt_onePointSixTwo; linarith
  -- starts_low: initial tension = 0 < 1/φ
  have h_starts_low : (tensionProfile tragedy).initial < lowTensionThreshold := by
    unfold tensionProfile lowTensionThreshold
    rw [tragedy_initial_tension]
    exact h_inv_pos
  -- ends_low: final tension = 2.5 ≥ 1/φ (actually 2.5 > 1/φ)
  have h_not_ends_low : ¬((tensionProfile tragedy).final < lowTensionThreshold) := by
    unfold tensionProfile lowTensionThreshold
    rw [tragedy_final_tension]
    -- Need: ¬(2.5 < 1/φ), i.e., 1/φ ≤ 2.5
    -- Since φ > 1, we have 1/φ < 1 < 2.5
    push_neg
    have h1 : 1 / Constants.phi < 1 := by rw [div_lt_one h_phi_pos]; exact Constants.one_lt_phi
    linarith
  -- Now the if-then-else reduces: starts_low ∧ ¬ends_low → Tragedy
  simp only [lowTensionThreshold, highTensionThreshold] at *
  simp only [h_starts_low, h_not_ends_low, and_true, and_false, not_true_eq_false, not_false_eq_true,
    ite_true, ite_false, ↓reduceIte]

/-- **THEOREM**: Tragedy has no catharsis - tension only increases.
    The σ values [0, 0.3, 0.7, 1.2, 1.8, 2.5] are monotonically increasing.

    **Proof sketch**: Catharsis requires `before > highTensionThreshold` (> φ ≈ 1.618)
    AND `after < lowTensionThreshold` (< 1/φ ≈ 0.618).
    For tragedy, the tensions are [0, 0.3, 0.7, 1.2, 1.8, 2.5].
    - For i ∈ {0,1,2,3}: before < φ, so first condition fails
    - For i = 4: before = 1.8 > φ, but after = 2.5 > 1/φ, so second condition fails

    **STATUS**: Proof requires case analysis on indices with Real comparisons.
    The proof is straightforward but Lean4's handling of noncomputable Reals
    makes automation difficult. -/
theorem H_tragedy_no_catharsis : ¬arcHasCatharsis tragedy := by
  unfold arcHasCatharsis
  intro ⟨i, hi, hcat⟩
  unfold hasCatharsis at hcat
  simp only [tragedy, tragedyBeats, List.length_cons, List.length_nil] at hi
  -- hi says i + 1 < 6, so i < 5
  have hi' : i < 5 := Nat.lt_of_succ_lt_succ hi
  have hphi : Constants.phi > 1.5 := Constants.phi_gt_onePointFive
  have hphi_pos : Constants.phi > 0 := Constants.phi_pos
  have h_inv_phi : Constants.phi⁻¹ < 0.7 := by
    rw [inv_eq_one_div]
    have h1 : Constants.phi > 1.5 := Constants.phi_gt_onePointFive
    calc 1 / Constants.phi < 1 / 1.5 := by
           apply div_lt_div_of_pos_left one_pos (by norm_num : (0:ℝ) < 1.5)
           exact h1
         _ = 2/3 := by norm_num
         _ < 0.7 := by norm_num
  -- hcat is: before > φ ∧ after < 1/φ ∧ (before - after) > before/2
  obtain ⟨h_before, h_after, _⟩ := hcat
  simp only [highTensionThreshold, lowTensionThreshold] at h_before h_after
  -- Unfold the specific beat indices
  simp only [tragedy, tragedyBeats, plotTension, mkBeat, mkMoralState] at h_before h_after
  -- Case analysis on i ∈ {0,1,2,3,4}
  rcases i with _ | _ | _ | _ | _ | _
  -- i = 0: h_before says 0 > φ > 1.5, which is False
  all_goals simp only [List.get_cons_zero, List.get_cons_succ] at h_before h_after
  all_goals norm_num at h_before h_after
  all_goals linarith

-- Backward-compatible aliases
abbrev tragedy_is_tragedy := H_tragedy_is_tragedy
abbrev tragedy_no_catharsis := H_tragedy_no_catharsis

/-! ## Example 3: Comedy (Much Ado style) -/

/-- Comedy σ-trajectory: oscillations around zero -/
def comedyBeats : List NarrativeBeat := [
  mkBeat 0.0 1.0 0,
  mkBeat 0.3 1.1 8,
  mkBeat (-0.2) 1.0 16,  -- First complication resolved
  mkBeat 0.4 1.2 24,
  mkBeat (-0.1) 1.0 32,  -- Second complication resolved
  mkBeat 0.2 1.1 40,
  mkBeat 0.0 1.0 48      -- Happy ending
]

/-- Helper: comedy beat indices are strictly increasing -/
private lemma comedyBeats_ordered (i j : ℕ) (hij : i < j)
    (hi : i < comedyBeats.length) (hj : j < comedyBeats.length) :
    (comedyBeats.get ⟨i, hi⟩).beat_index < (comedyBeats.get ⟨j, hj⟩).beat_index := by
  simp only [comedyBeats, List.length_cons, List.length_nil] at hi hj
  interval_cases i <;> interval_cases j <;> simp_all [comedyBeats, mkBeat]

/-- Helper: all comedy beats have zero net skew -/
private lemma comedyBeats_admissible (b : NarrativeBeat) (hb : b ∈ comedyBeats) :
    net_skew b.state.ledger = 0 := by
  simp only [comedyBeats, List.mem_cons, List.mem_nil_iff, or_false] at hb
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl := hb
  all_goals exact placeholder_valid

/-- Comedy arc -/
def comedy : NarrativeArc := {
  beats := comedyBeats
  nonempty := List.cons_ne_nil _ _
  ordered := comedyBeats_ordered
  admissible := comedyBeats_admissible
}

/-- **THEOREM**: Comedy has low overall tension.
    The max |σ| is 0.4, well below φ ≈ 1.618.

    **Proof**: We show maxTension comedy ≤ 0.4 < φ = highTensionThreshold.
    The tension trajectory is [0, 0.3, 0.2, 0.4, 0.1, 0.2, 0], so max = 0.4. -/
theorem H_comedy_low_tension : maxTension comedy < highTensionThreshold := by
  unfold maxTension tensionTrajectory highTensionThreshold
  -- We need to show: (foldl max 0 tensions) < φ
  -- The max of tensions is 0.4 (from |0.4|), and 0.4 < 1.5 < φ
  have h_phi : Constants.phi > 1.5 := Constants.phi_gt_onePointFive
  -- Show the max tension is ≤ 0.4
  have h_max : List.foldl max (0 : ℝ) (comedy.beats.map plotTension) ≤ 0.4 := by
    simp only [comedy, comedyBeats, List.map, plotTension, mkBeat, mkMoralState, NarrativeArc.beats]
    -- Compute step by step
    simp only [List.foldl_cons, List.foldl_nil]
    -- foldl max 0 [0, 0.3, 0.2, 0.4, 0.1, 0.2, 0]
    -- = max (max (max (max (max (max (max 0 0) 0.3) 0.2) 0.4) 0.1) 0.2) 0
    -- = max (max (max (max (max (max 0 0.3) 0.2) 0.4) 0.1) 0.2) 0
    -- = max (max (max (max (max 0.3 0.2) 0.4) 0.1) 0.2) 0
    -- = max (max (max (max 0.3 0.4) 0.1) 0.2) 0
    -- = max (max (max 0.4 0.1) 0.2) 0
    -- = max (max 0.4 0.2) 0
    -- = max 0.4 0
    -- = 0.4
    norm_num [abs_of_nonneg, abs_of_nonpos, max_eq_left, max_eq_right]
  linarith

-- Backward-compatible alias
abbrev comedy_low_tension := H_comedy_low_tension

/-! ## Example 4: Rebirth (A Christmas Carol style) -/

/-- Rebirth σ-trajectory: Scrooge in A Christmas Carol

    For classifyPlot to return Rebirth:
    1. ¬starts_low: initial tension > 1/φ ≈ 0.618
    2. ends_low: final tension < 1/φ
    3. range > 2φ ≈ 3.236

    Trajectory: |0.8| → |−1.0| → |−2.0| → |−3.5| → |−2.0| → |−0.5| → |0|
              = 0.8 → 1.0 → 2.0 → 3.5 → 2.0 → 0.5 → 0
    - initial = 0.8 > 0.618 ✓ (¬starts_low)
    - final = 0 < 0.618 ✓ (ends_low)
    - range = 3.5 - 0 = 3.5 > 3.236 ✓ -/
def rebirthBeats : List NarrativeBeat := [
  mkBeat 0.8 1.0 0,      -- Starts in tension (|0.8| > 1/φ)
  mkBeat (-1.0) 0.9 8,   -- Beginning of descent
  mkBeat (-2.0) 0.7 16,  -- Deeper descent
  mkBeat (-3.5) 0.5 24,  -- Rock bottom (peak tension = 3.5)
  mkBeat (-2.0) 0.7 32,  -- Beginning of recovery
  mkBeat (-0.5) 0.9 40,  -- Recovery continues
  mkBeat 0.0 1.2 48      -- Transformed (|0| < 1/φ)
]

/-- Helper: rebirth beat indices are strictly increasing -/
private lemma rebirthBeats_ordered (i j : ℕ) (hij : i < j)
    (hi : i < rebirthBeats.length) (hj : j < rebirthBeats.length) :
    (rebirthBeats.get ⟨i, hi⟩).beat_index < (rebirthBeats.get ⟨j, hj⟩).beat_index := by
  simp only [rebirthBeats, List.length_cons, List.length_nil] at hi hj
  interval_cases i <;> interval_cases j <;> simp_all [rebirthBeats, mkBeat]

/-- Helper: all rebirth beats have zero net skew -/
private lemma rebirthBeats_admissible (b : NarrativeBeat) (hb : b ∈ rebirthBeats) :
    net_skew b.state.ledger = 0 := by
  simp only [rebirthBeats, List.mem_cons, List.mem_nil_iff, or_false] at hb
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl := hb
  all_goals exact placeholder_valid

/-- Rebirth arc -/
def rebirth : NarrativeArc := {
  beats := rebirthBeats
  nonempty := List.cons_ne_nil _ _
  ordered := rebirthBeats_ordered
  admissible := rebirthBeats_admissible
}

-- Helper lemmas for rebirth classification
private lemma rebirth_initial_tension : plotTension rebirth.initial = 0.8 := by
  unfold plotTension rebirth NarrativeArc.initial rebirthBeats mkBeat mkMoralState
  norm_num

private lemma rebirth_final_tension : plotTension rebirth.terminal = 0 := by
  unfold plotTension rebirth NarrativeArc.terminal rebirthBeats mkBeat mkMoralState
  norm_num

/-- **THEOREM**: Rebirth is classified correctly.
    Descent → transformation → ascent pattern.

    **Proof sketch**: For classifyPlot to return Rebirth:
    1. ¬starts_low: initial = |0.8| = 0.8 > 1/φ ≈ 0.618 ✓
    2. ends_low: final = |0| = 0 < 1/φ ✓
    3. range = 3.5 - 0 = 3.5 > 2φ ≈ 3.236 ✓ -/
theorem H_rebirth_is_rebirth : classifyPlot rebirth = .Rebirth := by
  unfold classifyPlot
  -- Key threshold facts
  have hphi_pos : Constants.phi > 0 := Constants.phi_pos
  have hphi_gt : Constants.phi > 1.5 := Constants.phi_gt_onePointFive
  have hphi_lt : Constants.phi < 1.62 := Constants.phi_lt_onePointSixTwo
  have h_inv_lt : 1 / Constants.phi < 0.8 := by
    have h1 : Constants.phi > 1.5 := hphi_gt
    have h2 : 0.8 * Constants.phi > 0.8 * 1.5 := by nlinarith
    have h3 : 0.8 * Constants.phi > 1.2 := by linarith
    have h4 : 0.8 * Constants.phi > 1 := by linarith
    calc 1 / Constants.phi < 1 / 1.5 := by
           apply div_lt_div_of_pos_left one_pos (by norm_num : (0:ℝ) < 1.5) h1
         _ = 2/3 := by norm_num
         _ < 0.8 := by norm_num
  have h_inv_pos : 1 / Constants.phi > 0 := div_pos one_pos hphi_pos
  -- ¬starts_low: initial = 0.8 > 1/φ ≈ 0.618
  have h_not_starts_low : ¬((tensionProfile rebirth).initial < lowTensionThreshold) := by
    unfold tensionProfile lowTensionThreshold
    rw [rebirth_initial_tension]
    push_neg
    have h1 : 1 / Constants.phi < 0.8 := h_inv_lt
    linarith
  -- ends_low: final = 0 < 1/φ
  have h_ends_low : (tensionProfile rebirth).final < lowTensionThreshold := by
    unfold tensionProfile lowTensionThreshold
    rw [rebirth_final_tension]
    exact h_inv_pos
  -- range > 2φ: range = 3.5 - 0 = 3.5 > 3.24 ≈ 2φ
  have h_range : (tensionProfile rebirth).range > 2 * Constants.phi := by
    -- First compute peak = 3.5 and min = 0
    have h_peak : (accumulateTension rebirth).peak = 3.5 := by
      unfold accumulateTension rebirth rebirthBeats
      simp only [List.foldl, TensionAccumulator.addBeat, TensionAccumulator.empty]
      simp only [plotTension, mkBeat, mkMoralState]
      norm_num [max_def]
    have h_min : (tensionTrajectory rebirth).foldl min 3.5 = 0 := by
      unfold tensionTrajectory rebirth rebirthBeats plotTension mkBeat mkMoralState
      simp only [List.map, List.foldl]
      norm_num [min_def]
    unfold tensionProfile
    simp only [h_peak, h_min]
    -- range = 3.5 - 0 = 3.5 > 2φ ≈ 3.236
    have h1 : 2 * Constants.phi < 3.24 := by nlinarith
    linarith
  -- Now classify: ¬starts_low ∧ ends_low ∧ range > 2φ → Rebirth
  simp only [lowTensionThreshold, highTensionThreshold] at *
  simp only [h_not_starts_low, h_ends_low, h_range, not_false_eq_true, and_true, ite_true, ite_false,
    and_false, not_true_eq_false, ↓reduceIte]

-- Backward-compatible alias
abbrev rebirth_is_rebirth := H_rebirth_is_rebirth

/-! ## Arc Comparison Theorems -/

/-- A resolved arc has lower terminal tension than an unresolved one -/
theorem resolved_lower_terminal (arc1 arc2 : NarrativeArc)
    (h1 : plotTension arc1.terminal < lowTensionThreshold)
    (h2 : plotTension arc2.terminal > highTensionThreshold) :
    plotTension arc1.terminal < plotTension arc2.terminal := by
  have h_gap : lowTensionThreshold < highTensionThreshold := by
    unfold lowTensionThreshold highTensionThreshold
    have hphi : Constants.phi > 1 := Constants.one_lt_phi
    calc 1 / Constants.phi < 1 := by
           rw [div_lt_one Constants.phi_pos]
           exact hphi
      _ < Constants.phi := hphi
  linarith

/-! ## Status -/

def examples_status : String :=
  "╔══════════════════════════════════════════════════════════════╗\n" ++
  "║         NARRATIVE EXAMPLES - Concrete Story Instances         ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  ✓ mkBeat : helper for creating beats                         ║\n" ++
  "║  ✓ herosJourney : 8-beat Hero's Journey arc (THEOREM)         ║\n" ++
  "║  ✓ tragedy : 6-beat Tragedy arc (THEOREM)                     ║\n" ++
  "║  ✓ comedy : 7-beat Comedy arc (THEOREM)                       ║\n" ++
  "║  ✓ rebirth : 7-beat Rebirth arc (THEOREM)                     ║\n" ++
  "║  ✓ resolved_lower_terminal : PROVEN                           ║\n" ++
  "║  ⚪ Classification theorems : AXIOM (noncomputable)           ║\n" ++
  "║  ✓ Ordering/admissibility : PROVEN (fin_cases)                ║\n" ++
  "╚══════════════════════════════════════════════════════════════╝"

#eval examples_status

end

end Examples
end Narrative
end IndisputableMonolith
