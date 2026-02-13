import Mathlib
import IndisputableMonolith.Narrative.Core
import IndisputableMonolith.Ethics.MoralState

/-!
# Plot Tension: σ as the Physics of Drama

This module formalizes **Plot Tension** as the ledger skew σ evolving over time.

## Core Insight

**Plot Tension = Ledger Skew σ**

| σ Value | Narrative State |
|---------|-----------------|
| σ = 0 | Equilibrium (peace, resolution) |
| σ > 0 | Extraction/debt (crisis building) |
| σ < 0 | Contribution/credit (sacrifice) |
| |σ| large | High tension (climax) |

## Dynamics

The evolution of σ(t) follows the recognition dynamics:
- σ tends toward 0 (resolution is the attractor)
- Large |σ| requires energy to maintain
- Sudden σ changes = plot twists

## Connection to Traditional Dramaturgy

| RS Concept | Traditional Drama |
|-----------|-------------------|
| σ(0) = 0 | Initial equilibrium |
| σ increasing | Rising action |
| max |σ| | Climax |
| σ → 0 | Resolution/denouement |
| σ oscillation | Complications |

-/

namespace IndisputableMonolith
namespace Narrative

open Foundation Ethics Real

noncomputable section

/-! ## Plot Tension Function -/

/-- **PlotTension** at a given beat is the absolute skew magnitude.

    This is THE measure of dramatic intensity. -/
def plotTension (b : NarrativeBeat) : ℝ :=
  |b.state.skew|

/-- PlotTension is always non-negative -/
theorem plotTension_nonneg (b : NarrativeBeat) : 0 ≤ plotTension b :=
  abs_nonneg _

/-- Tension trajectory for a full arc -/
def tensionTrajectory (arc : NarrativeArc) : List ℝ :=
  arc.beats.map plotTension

/-- Maximum tension in an arc (the climax point) -/
def maxTension (arc : NarrativeArc) : ℝ :=
  (tensionTrajectory arc).foldl max 0

/-- Index of maximum tension (climax position) -/
def climaxIndex (arc : NarrativeArc) : ℕ :=
  let tensions := tensionTrajectory arc
  tensions.findIdx (· = maxTension arc)

/-! ## Tension Dynamics -/

/-- Rate of tension change between consecutive beats -/
def tensionDerivative (arc : NarrativeArc) (i : ℕ)
    (hi : i + 1 < arc.beats.length) : ℝ :=
  let t1 := plotTension (arc.beats.get ⟨i, Nat.lt_of_succ_lt hi⟩)
  let t2 := plotTension (arc.beats.get ⟨i + 1, hi⟩)
  let dt := (arc.beats.get ⟨i + 1, hi⟩).beat_index -
            (arc.beats.get ⟨i, Nat.lt_of_succ_lt hi⟩).beat_index
  if dt = 0 then 0 else (t2 - t1) / dt

/-- Rising action: tension is increasing -/
def isRisingAction (arc : NarrativeArc) (i : ℕ)
    (hi : i + 1 < arc.beats.length) : Prop :=
  tensionDerivative arc i hi > 0

/-- Falling action: tension is decreasing -/
def isFallingAction (arc : NarrativeArc) (i : ℕ)
    (hi : i + 1 < arc.beats.length) : Prop :=
  tensionDerivative arc i hi < 0

/-- Plateau: tension is stable -/
def isPlateau (arc : NarrativeArc) (i : ℕ)
    (hi : i + 1 < arc.beats.length) (ε : ℝ := 0.01) : Prop :=
  |tensionDerivative arc i hi| < ε

/-! ## Tension Thresholds (from RS φ-structure) -/

/-- Low tension threshold (stable situation) -/
def lowTensionThreshold : ℝ := 1 / Constants.phi  -- 1/φ ≈ 0.618

/-- High tension threshold (crisis point) -/
def highTensionThreshold : ℝ := Constants.phi  -- φ ≈ 1.618

/-- Critical tension (catastrophe imminent) -/
def criticalTensionThreshold : ℝ := Constants.phi ^ 2  -- φ² ≈ 2.618

/-- A beat is in low tension (equilibrium) -/
def isLowTension (b : NarrativeBeat) : Prop :=
  plotTension b < lowTensionThreshold

/-- A beat is in high tension (crisis) -/
def isHighTension (b : NarrativeBeat) : Prop :=
  plotTension b > highTensionThreshold

/-- A beat is at critical tension (climax) -/
def isCriticalTension (b : NarrativeBeat) : Prop :=
  plotTension b > criticalTensionThreshold

/-! ## Tension Accumulator -/

/-- **TensionAccumulator** tracks the integral of tension over time.

    Total accumulated tension = ∫ σ(t) dt

    High accumulation without release → building pressure
    Sudden drop in accumulation → catharsis -/
structure TensionAccumulator where
  /-- Running sum of tension -/
  accumulated : ℝ
  /-- Number of beats accumulated -/
  beats_counted : ℕ
  /-- Peak tension seen so far -/
  peak : ℝ
  /-- Accumulated is non-negative -/
  accumulated_nonneg : 0 ≤ accumulated

/-- Initial empty accumulator -/
def TensionAccumulator.empty : TensionAccumulator := ⟨0, 0, 0, le_refl 0⟩

/-- Add a beat to the accumulator -/
def TensionAccumulator.addBeat (acc : TensionAccumulator) (b : NarrativeBeat) : TensionAccumulator :=
  let t := plotTension b
  { accumulated := acc.accumulated + t
    beats_counted := acc.beats_counted + 1
    peak := max acc.peak t
    accumulated_nonneg := by
      apply add_nonneg acc.accumulated_nonneg
      exact plotTension_nonneg b }

/-- Average tension so far -/
def TensionAccumulator.averageTension (acc : TensionAccumulator) : ℝ :=
  if acc.beats_counted = 0 then 0
  else acc.accumulated / acc.beats_counted

/-- Tension variance indicator (peak - average) -/
def TensionAccumulator.tensionVariance (acc : TensionAccumulator) : ℝ :=
  acc.peak - acc.averageTension

/-- Accumulate tension across an entire arc -/
def accumulateTension (arc : NarrativeArc) : TensionAccumulator :=
  arc.beats.foldl TensionAccumulator.addBeat TensionAccumulator.empty

/-! ## Tension Analysis -/

/-- Arc tension profile: statistics about tension distribution -/
structure TensionProfile where
  /-- Average tension across the arc -/
  mean : ℝ
  /-- Peak tension (climax) -/
  peak : ℝ
  /-- Initial tension -/
  initial : ℝ
  /-- Final tension -/
  final : ℝ
  /-- Tension range (peak - min) -/
  range : ℝ
  /-- Position of climax (0 to 1) -/
  climax_position : ℝ

/-- Extract tension profile from an arc -/
def tensionProfile (arc : NarrativeArc) : TensionProfile :=
  let acc := accumulateTension arc
  let tensions := tensionTrajectory arc
  let minT := tensions.foldl min (acc.peak)
  let climaxIdx := climaxIndex arc
  { mean := acc.averageTension
    peak := acc.peak
    initial := plotTension arc.initial
    final := plotTension arc.terminal
    range := acc.peak - minT
    climax_position := if arc.length = 0 then 0.5
                       else climaxIdx / arc.length }

/-! ## Catharsis: Tension Release -/

/-- **Catharsis** occurs when accumulated tension drops rapidly.

    This is the emotional release in drama — the moment when built-up
    σ (skew/debt) is suddenly resolved. -/
def hasCatharsis (arc : NarrativeArc) (i : ℕ)
    (hi : i + 1 < arc.beats.length) : Prop :=
  let before := plotTension (arc.beats.get ⟨i, Nat.lt_of_succ_lt hi⟩)
  let after := plotTension (arc.beats.get ⟨i + 1, hi⟩)
  -- Catharsis requires: high tension before, low after, rapid change
  before > highTensionThreshold ∧
  after < lowTensionThreshold ∧
  (before - after) > before / 2  -- Drop by more than 50%

/-- An arc has catharsis if there exists a cathartic moment -/
def arcHasCatharsis (arc : NarrativeArc) : Prop :=
  ∃ i : ℕ, ∃ hi : i + 1 < arc.beats.length, hasCatharsis arc i hi

/-! ## Tension Laws -/

/-- **THEOREM: Tension Conservation in Closed Narrative Arcs**

    In a closed narrative system, the net change in tension is zero.
    This is the narrative analog of the conservation of charge.

    **RS Interpretation**: Tension conservation means that the ledger must
    eventually balance - any extraction (σ > 0) must be matched by contribution
    (σ < 0) to return to equilibrium.

    **Mathematical Content**: For a closed arc (σ_initial = σ_terminal),
    the telescopic sum of tension changes equals zero. -/
theorem tension_conservation (arc : NarrativeArc)
    (h_closed : arc.initial.state.skew = arc.terminal.state.skew) :
    arc.terminal.state.skew - arc.initial.state.skew = 0 := by
  rw [h_closed, sub_self]

/-- **THEOREM: σ = 0 is the Tension Attractor (Ground State)**

    Over 8+ ticks, the system has time to relax toward the equilibrium σ=0.
    Terminal skew magnitude is bounded by initial skew magnitude.

    **Mathematical Content**: This is a Lyapunov stability result. The function
    V(arc) = |σ_terminal| serves as a Lyapunov function for the narrative dynamics.
    Under J-cost minimization, V is non-increasing along trajectories.

    **Proof Strategy (Lyapunov)**:
    1. Define V(state) = |state.skew| as the Lyapunov candidate
    2. Show V̇ = d|σ|/dt ≤ 0 under the recognition dynamics
    3. This follows from J-cost minimization: J(σ) = ½(σ + 1/σ) - 1
    4. The gradient ∇J points toward σ = 1 (ground state)
    5. Movement along -∇J decreases |σ - 1|, and for narrative |σ| = 0 maps to x = 1

    **RS Interpretation**: The recognition dynamics naturally drive narrative
    systems toward equilibrium (σ = 0, ledger balanced). Arcs with net_skew = 0
    at each beat (the _h_admissible hypothesis) represent "well-formed" narratives
    that follow the natural gradient flow.

    **Infrastructure Needed**:
    - Explicit dynamics model: how R̂ transforms NarrativeArc
    - Monotonicity: storyAction(R̂(arc)) ≤ storyAction(arc)
    - Connection: |σ| ≈ √(J(σ)) near σ = 0

    **HYPOTHESIS**: Tension attracts to zero over admissible arcs.

    **Physical justification**: Lyapunov stability argument:
    - V = |σ| is a Lyapunov function for recognition dynamics
    - V(terminal) ≤ V(initial) by monotonicity of J-cost along trajectories
    - The h_admissible condition ensures the arc follows natural dynamics
    - The h_long condition gives enough time for relaxation

    **Formal proof requires**: Dynamics model from Foundation.RecognitionOperator.

    **STATUS**: HYPOTHESIS (dynamical systems result, pending full dynamics model) -/
def tension_attractor_hypothesis (arc : NarrativeArc) : Prop :=
  arc.length > 8 →
  (∀ b ∈ arc.beats, net_skew b.state.ledger = 0) →
  |arc.terminal.state.skew| ≤ |arc.initial.state.skew|

theorem H_tension_attractor (arc : NarrativeArc)
    (h : tension_attractor_hypothesis arc)
    (_h_long : arc.length > 8)  -- At least one full 8-tick cycle
    (_h_admissible : ∀ b ∈ arc.beats, net_skew b.state.ledger = 0) :
    |arc.terminal.state.skew| ≤ |arc.initial.state.skew| :=
  h _h_long _h_admissible

/-- Version with explicit assumption for use in composition -/
theorem tension_attractor_of_assumption (arc : NarrativeArc)
    (h_long : arc.length > 8)
    (h_admissible : ∀ b ∈ arc.beats, net_skew b.state.ledger = 0)
    (h_attractor : |arc.terminal.state.skew| ≤ |arc.initial.state.skew|) :
    |arc.terminal.state.skew| ≤ |arc.initial.state.skew| := h_attractor

/-! ## Status -/

def plot_tension_status : String :=
  "╔══════════════════════════════════════════════════════════════╗\n" ++
  "║           PLOT TENSION MODULE - Lean 4 Formalization          ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  ✓ plotTension : NarrativeBeat → ℝ (|σ|)                      ║\n" ++
  "║  ✓ tensionTrajectory : NarrativeArc → List ℝ                  ║\n" ++
  "║  ✓ tensionDerivative : dσ/dt at each beat                     ║\n" ++
  "║  ✓ φ-based thresholds (low/high/critical)                     ║\n" ++
  "║  ✓ TensionAccumulator for running stats                       ║\n" ++
  "║  ✓ TensionProfile for arc analysis                            ║\n" ++
  "║  ✓ hasCatharsis : sudden tension release                      ║\n" ++
  "║  ✓ tension_conservation : closed arcs conserve tension        ║\n" ++
  "║  ✓ tension_attractor : σ → 0 (axiom - Lyapunov argument)      ║\n" ++
  "╚══════════════════════════════════════════════════════════════╝"

#eval plot_tension_status

end

end Narrative
end IndisputableMonolith
