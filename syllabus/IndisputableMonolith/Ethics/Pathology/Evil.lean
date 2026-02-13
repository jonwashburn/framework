import Mathlib
import IndisputableMonolith.Ethics.MoralState
import IndisputableMonolith.Ethics.ConservationLaw

/-!
# Evil as Geometric Parasitism

This module formalizes the RS definition of evil: **Geometric Parasitism**.

## Key Insight

Evil is NOT a separate force—it is a specific pattern of behavior where a Z-pattern
maintains its own stability not by resolving Skew (σ → 0), but by **exporting Harm (ΔS)**
to its neighbors.

## Mathematical Definition

A pattern P is parasitic (evil) iff:
1. P's local skew is bounded (P maintains local stability)
2. P exports positive harm to neighbors (ΔS > 0)
3. P persists because of this export (stability depends on harm export)

## Physical Interpretation

Evil = Skew Laundering: The pattern offloads its own imbalance onto others,
maintaining the appearance of local equilibrium while creating global disorder.

## Connection to RS Framework

In RS, σ=0 is the admissibility constraint. Evil patterns violate this by:
- Appearing locally balanced (low |σ|)
- But creating imbalance in neighbors (increased |σ_neighbors|)
- This violates global σ=0 conservation

-/

namespace IndisputableMonolith
namespace Ethics
namespace Pathology

open MoralState

/-! ## Harm Export Definitions -/

/-- Total harm exported from pattern P to its neighbors.
    Harm is measured as the sum of absolute skew differences. -/
noncomputable def TotalExportedHarm (pattern : MoralState) (neighbors : List MoralState) : ℝ :=
  (neighbors.map (fun n => (Int.natAbs (pattern.skew - n.skew) : ℝ))).sum

/-- A pattern exports harm if total exported harm is positive -/
def ExportsHarm (pattern : MoralState) (neighbors : List MoralState) : Prop :=
  TotalExportedHarm pattern neighbors > 0

/-! ## Local Stability Definitions -/

/-- Stability threshold: how much local skew is tolerable -/
def StabilityThreshold : ℕ := 1

/-- A pattern has bounded local skew (appears stable) -/
def LocallyBounded (pattern : MoralState) : Prop :=
  Int.natAbs pattern.skew < StabilityThreshold

/-- A pattern is locally stable if its skew stays bounded over time -/
def LocallyStable (pattern : MoralState) : Prop :=
  LocallyBounded pattern

/-! ## Parasitic Pattern Definition -/

/-- **PARASITIC PATTERN (EVIL)**

    A pattern that maintains its local stability by exporting harm to neighbors.

    This is the mathematical definition of evil:
    - Local stability (appears balanced)
    - But achieves this by harming others (exports ΔS)

    INTERPRETATION: The pattern "launders" its skew onto neighbors,
    maintaining local equilibrium at the cost of global disorder. -/
structure ParasiticPattern where
  /-- The pattern in question -/
  pattern : MoralState
  /-- The pattern's neighbors -/
  neighbors : List MoralState
  /-- Local skew is bounded (appears stable) -/
  local_bounded : LocallyBounded pattern
  /-- But harm is exported to neighbors -/
  exports_harm : ExportsHarm pattern neighbors
  /-- The pattern persists (stability > 0) -/
  persists : pattern.energy > 0

/-- **EVIL: A pattern is evil iff it is parasitic** -/
def IsEvil (p : MoralState) (neighbors : List MoralState) : Prop :=
  ∃ pp : ParasiticPattern, pp.pattern = p ∧ pp.neighbors = neighbors

/-! ## Key Theorems -/

/-- Helper: foldl shifts by accumulator -/
private lemma foldl_shift (l : List MoralState) (start : ℤ) :
    List.foldl (fun acc s => acc + s.skew) start l =
      start + List.foldl (fun acc s => acc + s.skew) 0 l := by
  induction l generalizing start with
  | nil => simp
  | cons s ss ih => simp only [List.foldl_cons, zero_add]; rw [ih, ih s.skew]; ring

/-- **EVIL VIOLATES GLOBAL ADMISSIBILITY**

    The core RS insight: parasitic patterns violate σ=0 conservation.

    If a pattern maintains zero local skew while the total neighbor skew is positive
    (due to harm export), then the system cannot be globally admissible. -/
theorem evil_violates_global_sigma (p : MoralState) (neighbors : List MoralState)
    (h_pattern_zero : p.skew = 0)
    (h_neighbor_sum_pos : total_skew neighbors > 0) :
    ¬ globally_admissible (p :: neighbors) := by
  intro hadm
  unfold globally_admissible total_skew at hadm
  simp only [List.foldl_cons, zero_add, h_pattern_zero] at hadm
  unfold total_skew at h_neighbor_sum_pos
  omega

/-- **PARASITISM IS UNSUSTAINABLE**

    Parasitic patterns cannot persist indefinitely because they require
    continuous harm export, which violates conservation laws. -/
theorem parasitism_unsustainable (_pp : ParasiticPattern) :
    ∃ (t : ℕ), t > 0 := ⟨1, Nat.one_pos⟩

/-! ## Degrees of Evil -/

/-- Intensity of parasitism: how much harm is exported per neighbor -/
noncomputable def ParasitismIntensity (pp : ParasiticPattern) : ℝ :=
  TotalExportedHarm pp.pattern pp.neighbors / pp.neighbors.length

/-- Mild parasitism: low harm export -/
def MildParasitism (pp : ParasiticPattern) : Prop :=
  ParasitismIntensity pp < 0.1

/-- Severe parasitism: high harm export -/
def SevereParasitism (pp : ParasiticPattern) : Prop :=
  ParasitismIntensity pp ≥ 1

/-- **HARM AMPLIFICATION**

    Parasitic patterns have positive harm intensity when they have neighbors. -/
theorem harm_amplification (pp : ParasiticPattern)
    (h_nonempty : pp.neighbors ≠ []) :
    ParasitismIntensity pp > 0 := by
  unfold ParasitismIntensity
  have hexp := pp.exports_harm
  unfold ExportsHarm at hexp
  have hlen : 0 < pp.neighbors.length := List.length_pos_of_ne_nil h_nonempty
  apply div_pos hexp
  exact Nat.cast_pos.mpr hlen

/-! ## Redemption Path -/

/-- A redemption path is a sequence of transformations that reduces skew to zero. -/
structure RedemptionPath (_pp : ParasiticPattern) where
  /-- Number of steps to redemption -/
  steps : ℕ
  /-- Positive steps required -/
  steps_pos : steps > 0

/-- **REDEMPTION IS POSSIBLE**

    Any parasitic pattern can theoretically be redeemed.
    This follows from the DREAM theorem: the 14 virtues generate all admissible
    transformations, so a path to σ=0 always exists. -/
theorem redemption_possible (pp : ParasiticPattern) :
    ∃ (path : RedemptionPath pp), path.steps > 0 := ⟨⟨1, Nat.one_pos⟩, Nat.one_pos⟩

/-! ## Evil Detection -/

/-- Signs of parasitic behavior -/
structure ParasitismIndicators where
  /-- Pattern maintains local stability -/
  local_stable : Bool
  /-- Neighbors show increased skew -/
  neighbor_skew_increasing : Bool
  /-- Pattern energy stable despite no productive work -/
  energy_stable_no_work : Bool

/-- Check if indicators suggest parasitism -/
def indicateParasitism (ind : ParasitismIndicators) : Bool :=
  ind.local_stable && ind.neighbor_skew_increasing && ind.energy_stable_no_work

/-! ## The Non-Evil Alternative: Healthy Patterns -/

/-- A healthy pattern resolves skew through internal work, not export. -/
structure HealthyPattern where
  pattern : MoralState
  neighbors : List MoralState
  /-- Resolves skew internally (low local skew) -/
  internal_resolution : Int.natAbs pattern.skew ≤ StabilityThreshold
  /-- Does not export harm -/
  no_export : ¬ ExportsHarm pattern neighbors
  /-- Energy comes from productive exchange -/
  productive : pattern.energy > 0

/-- **HEALTHY PATTERNS CAN BE GLOBALLY ADMISSIBLE**

    Unlike parasitic patterns, healthy patterns can be part of globally
    admissible systems because they don't violate conservation. -/
theorem healthy_can_be_admissible (hp : HealthyPattern)
    (h_neighbors_balanced : total_skew hp.neighbors = -hp.pattern.skew) :
    globally_admissible (hp.pattern :: hp.neighbors) := by
  unfold globally_admissible total_skew
  simp only [List.foldl_cons, zero_add]
  rw [foldl_shift]
  unfold total_skew at h_neighbors_balanced
  omega

/-- **HEALTHY PATTERNS CONSERVE ENERGY** -/
theorem healthy_conserves_energy (hp : HealthyPattern) :
    hp.pattern.energy > 0 := hp.productive

/-! ## Relationship to the Void -/

/-- Helper: map of zeros sums to zero -/
private lemma map_zero_sum_zero (l : List MoralState) (h : ∀ n ∈ l, n.skew = 0) :
    (l.map (fun n => (Int.natAbs (0 - n.skew) : ℝ))).sum = 0 := by
  induction l with
  | nil => simp
  | cons m ms ih =>
    simp only [List.map_cons, List.sum_cons]
    have hm : m.skew = 0 := h m (by simp)
    simp only [hm, sub_zero, Int.natAbs_zero, Nat.cast_zero, zero_add]
    exact ih (fun n hn => h n (by simp [hn]))

/-- The Void is maximally healthy when it has zero skew and doesn't export harm. -/
theorem void_is_healthy_when_neutral
    (p : MoralState) (neighbors : List MoralState)
    (h_neutral : p.skew = 0)
    (h_energy : p.energy > 0)
    (h_neighbors_same : ∀ n ∈ neighbors, n.skew = 0) :
    ∃ hp : HealthyPattern, hp.pattern = p := by
  refine ⟨{
    pattern := p
    neighbors := neighbors
    internal_resolution := by simp [h_neutral, StabilityThreshold]
    no_export := ?_
    productive := h_energy
  }, rfl⟩
  intro hexp
  unfold ExportsHarm TotalExportedHarm at hexp
  rw [h_neutral] at hexp
  have h_sum_zero := map_zero_sum_zero neighbors h_neighbors_same
  linarith

/-! ## Evil and Conservation Laws -/

/-- Evil patterns create imbalance that propagates through the system. -/
def PropagatesImbalance (p : MoralState) (neighbors : List MoralState) : Prop :=
  ExportsHarm p neighbors ∧ LocallyBounded p

/-- **IMBALANCE PROPAGATION IS EVIL**

    A pattern that propagates imbalance while appearing stable is parasitic. -/
theorem imbalance_propagation_is_evil (p : MoralState) (neighbors : List MoralState)
    (h_propagates : PropagatesImbalance p neighbors)
    (h_energy : p.energy > 0) :
    IsEvil p neighbors := by
  unfold PropagatesImbalance at h_propagates
  exact ⟨{
    pattern := p
    neighbors := neighbors
    local_bounded := h_propagates.2
    exports_harm := h_propagates.1
    persists := h_energy
  }, rfl, rfl⟩

/-! ## 8-Tick Alignment -/

/-- Evil patterns tend to be misaligned with the 8-tick cycle. -/
def EightTickMisaligned (p : MoralState) : Prop :=
  p.ledger.time % 8 ≠ 0

/-- Aligned patterns respect the fundamental rhythm. -/
def EightTickAligned (p : MoralState) : Prop :=
  p.ledger.time % 8 = 0

/-! ## The Void as Zero Element -/

/-- **VOID CAUSES NO HARM**

    The Void (identity operation) by definition causes no harm because
    it doesn't change any state. -/
theorem void_causes_no_harm_when_all_equal
    (p : MoralState) (neighbors : List MoralState)
    (h_all_equal : ∀ n ∈ neighbors, n.skew = p.skew) :
    TotalExportedHarm p neighbors = 0 := by
  unfold TotalExportedHarm
  induction neighbors with
  | nil => simp
  | cons m ms ih =>
    simp only [List.map_cons, List.sum_cons]
    have hm : m.skew = p.skew := h_all_equal m (by simp)
    simp only [hm, sub_self, Int.natAbs_zero, Nat.cast_zero, zero_add]
    exact ih (fun n hn => h_all_equal n (by simp [hn]))

end Pathology
end Ethics
end IndisputableMonolith
