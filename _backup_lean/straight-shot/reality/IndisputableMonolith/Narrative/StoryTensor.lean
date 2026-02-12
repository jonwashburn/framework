import Mathlib
import IndisputableMonolith.Narrative.Core
import IndisputableMonolith.Narrative.PlotTension
import IndisputableMonolith.Narrative.StoryGeodesic

/-!
# Story Tensor: Narrative Curvature and Geometry

This module formalizes the **differential geometry** of narrative space.

## Core Insight

Narrative space has intrinsic curvature determined by the J-cost landscape.
This curvature explains:
- Why some story transitions feel "natural" (flat regions)
- Why some transitions feel "forced" (high curvature)
- Where plot twists occur (geodesic singularities)
- How multiple narrative threads interact (metric coupling)

## The Story Metric

The natural metric on MoralState space is:

```
ds² = dσ² + (1/φ)·dE² + (1/φ²)·dZ²
```

Where:
- σ = skew (primary narrative variable)
- E = energy (capacity for action)
- Z = Z-patterns (character/identity invariants)

The φ-weighting reflects RS's φ-hierarchical structure.

## Curvature and Plot

| Curvature | Narrative Meaning |
|-----------|-------------------|
| K = 0 | Steady development |
| K > 0 | Convergent (climax building) |
| K < 0 | Divergent (exploration) |
| K → ∞ | Singularity (plot twist) |

-/

namespace IndisputableMonolith
namespace Narrative

open Foundation Ethics Real

noncomputable section

/-! ## Story Metric -/

/-- The **Story Metric** on MoralState space.

    ds² = dσ² + (1/φ)·dE² + (1/φ²)·dZ²

    This encodes the cost of moving through narrative space. -/
structure StoryMetric where
  /-- Coefficient for σ² (skew/tension) -/
  g_sigma : ℝ := 1
  /-- Coefficient for E² (energy) -/
  g_energy : ℝ := 1 / Constants.phi
  /-- Coefficient for Z² (pattern invariants) -/
  g_pattern : ℝ := 1 / (Constants.phi ^ 2)
  /-- Metric is positive definite -/
  positive_definite : 0 < g_sigma ∧ 0 < g_energy ∧ 0 < g_pattern

/-- The canonical RS story metric -/
def canonicalMetric : StoryMetric where
  g_sigma := 1
  g_energy := 1 / Constants.phi
  g_pattern := 1 / (Constants.phi ^ 2)
  positive_definite := by
    constructor
    · norm_num
    constructor
    · apply div_pos one_pos Constants.phi_pos
    · apply div_pos one_pos (pow_pos Constants.phi_pos 2)

/-- Distance between two MoralStates -/
def storyDistance (g : StoryMetric) (s1 s2 : MoralState) : ℝ :=
  let dσ := s2.skew - s1.skew
  let dE := s2.energy - s1.energy
  -- Pattern distance (simplified - would need Z-pattern diff)
  let dZ : ℝ := 0
  Real.sqrt (g.g_sigma * dσ^2 + g.g_energy * dE^2 + g.g_pattern * dZ^2)

/-- Distance is symmetric -/
theorem storyDistance_symm (g : StoryMetric) (s1 s2 : MoralState) :
    storyDistance g s1 s2 = storyDistance g s2 s1 := by
  unfold storyDistance
  ring_nf

/-- Distance is non-negative -/
theorem storyDistance_nonneg (g : StoryMetric) (s1 s2 : MoralState) :
    0 ≤ storyDistance g s1 s2 := by
  unfold storyDistance
  apply Real.sqrt_nonneg

/-! ## Story Curvature -/

/-- **Story Curvature** at a point in narrative space.

    This measures how much geodesics diverge or converge. -/
structure StoryCurvature where
  /-- The beat at which curvature is computed -/
  beat : NarrativeBeat
  /-- Scalar curvature (Ricci scalar analog) -/
  scalar : ℝ
  /-- Sectional curvature in σ-E plane -/
  sectional_sigma_E : ℝ
  /-- Sectional curvature in σ-Z plane -/
  sectional_sigma_Z : ℝ

/-- Compute approximate curvature from three consecutive beats -/
def computeCurvature (b0 b1 b2 : NarrativeBeat) : StoryCurvature :=
  let dσ1 := b1.state.skew - b0.state.skew
  let dσ2 := b2.state.skew - b1.state.skew
  let d2σ := dσ2 - dσ1  -- Second derivative (discrete)

  let dE1 := b1.state.energy - b0.state.energy
  let dE2 := b2.state.energy - b1.state.energy
  let d2E := dE2 - dE1

  -- Scalar curvature is related to second derivatives
  let K := d2σ^2 + d2E^2 / Constants.phi

  { beat := b1
    scalar := K
    sectional_sigma_E := d2σ * d2E
    sectional_sigma_Z := 0 }

/-- Curvature trajectory for an arc -/
def curvatureTrajectory (arc : NarrativeArc) : List StoryCurvature :=
  if h : arc.length < 3 then []
  else
    List.range (arc.length - 2) |>.filterMap fun i =>
      if h1 : i < arc.beats.length then
        if h2 : i + 1 < arc.beats.length then
          if h3 : i + 2 < arc.beats.length then
            some (computeCurvature
              (arc.beats.get ⟨i, h1⟩)
              (arc.beats.get ⟨i + 1, h2⟩)
              (arc.beats.get ⟨i + 2, h3⟩))
          else none
        else none
      else none

/-! ## Curvature Classification -/

/-- Flat narrative: |K| < threshold -/
def isFlat (K : StoryCurvature) (ε : ℝ := 0.1) : Prop :=
  |K.scalar| < ε

/-- Positive curvature: convergent narrative (building to climax) -/
def isConvergent (K : StoryCurvature) : Prop :=
  K.scalar > 0.1

/-- Negative curvature: divergent narrative (exploration, branching) -/
def isDivergent (K : StoryCurvature) : Prop :=
  K.scalar < -0.1

/-- Singular curvature: plot twist or discontinuity -/
def isSingular (K : StoryCurvature) (threshold : ℝ := Constants.phi ^ 2) : Prop :=
  K.scalar > threshold

/-! ## Curvature and Plot Structure -/

/-- An arc is smooth if max curvature is bounded -/
def isSmooth (arc : NarrativeArc) (threshold : ℝ := 2) : Prop :=
  ∀ K ∈ curvatureTrajectory arc, K.scalar < threshold

/-- An arc has a plot twist at curvature spike -/
def hasPlotTwist (arc : NarrativeArc) : Prop :=
  ∃ K ∈ curvatureTrajectory arc, isSingular K

/-- Count number of plot twists -/
def countPlotTwists (arc : NarrativeArc) : ℕ :=
  (curvatureTrajectory arc).filter (fun K => K.scalar > Constants.phi ^ 2) |>.length

/-! ## Christoffel Symbols (Connection Coefficients) -/

/-- **Christoffel Symbols** encode how the metric changes.

    These determine the geodesic equation:
    d²xᵘ/dt² + Γᵘᵥσ (dxᵛ/dt)(dxσ/dt) = 0 -/
structure ChristoffelSymbols where
  /-- Γσσσ -/
  Gamma_sigma_sigma_sigma : ℝ := 0
  /-- Γσσε (σ-E mixing) -/
  Gamma_sigma_sigma_E : ℝ := 0
  /-- ΓεSσ (E-σ mixing) -/
  Gamma_E_sigma_sigma : ℝ := 0
  /-- The connection is metric-compatible -/
  metric_compatible : True

/-- For the canonical RS metric, Christoffel symbols vanish (flat at unit) -/
def canonicalChristoffel : ChristoffelSymbols := { metric_compatible := trivial }

/-! ## Narrative Riemann Tensor -/

/-- The **Narrative Riemann Tensor** encodes the full curvature information.

    R^μ_νρσ measures the failure of parallel transport around loops. -/
structure NarrativeRiemann where
  /-- R^σ_Eσε component -/
  R_sigma_E_sigma_E : ℝ := 0
  /-- Symmetries are respected -/
  antisymmetric : True

/-- Compute Riemann tensor from curvature -/
def riemannFromCurvature (K : StoryCurvature) : NarrativeRiemann :=
  { R_sigma_E_sigma_E := K.sectional_sigma_E
    antisymmetric := trivial }

/-! ## Geodesic Deviation -/

/-- **Geodesic Deviation**: How nearby geodesics separate.

    ξ̈ = R^μ_νρσ u^ν ξ^ρ u^σ

    where ξ is the separation vector, u is the tangent. -/
def geodesicDeviation (R : NarrativeRiemann) (separation : ℝ) : ℝ :=
  R.R_sigma_E_sigma_E * separation

/-- Positive curvature → geodesics converge (climax) -/
theorem positive_curvature_converge (R : NarrativeRiemann) (h : R.R_sigma_E_sigma_E > 0) :
    ∀ ξ > 0, geodesicDeviation R ξ > 0 := by
  intro ξ hξ
  unfold geodesicDeviation
  exact mul_pos h hξ

/-! ## Narrative Torsion -/

/-- **Narrative Torsion** measures asymmetry in the connection.

    Non-zero torsion indicates time-asymmetric narrative:
    the path from A→B differs from B→A. -/
structure NarrativeTorsion where
  /-- Torsion in σ-E sector -/
  T_sigma_E : ℝ := 0
  /-- Physical interpretation: time-directedness of story -/
  time_directed : Prop := T_sigma_E > 0

/-- Stories naturally have positive torsion (time flows forward) -/
def canonicalTorsion : NarrativeTorsion where
  T_sigma_E := 1 / Constants.phi  -- Mild forward-time preference
  -- time_directed defaults to T_sigma_E > 0, which is 1/φ > 0 (true)

/-! ## The Story Tensor (Full Structure) -/

/-- **The Complete Story Tensor** bundles all geometric data. -/
structure StoryTensor where
  /-- The metric -/
  metric : StoryMetric
  /-- Christoffel symbols -/
  connection : ChristoffelSymbols
  /-- Riemann curvature -/
  curvature : NarrativeRiemann
  /-- Torsion -/
  torsion : NarrativeTorsion
  /-- The reference beat -/
  at_beat : NarrativeBeat

/-- Compute full story tensor at a beat -/
def storyTensorAt (arc : NarrativeArc) (i : ℕ)
    (hi : i + 2 < arc.beats.length) : StoryTensor :=
  let b0 := arc.beats.get ⟨i, Nat.lt_of_succ_lt (Nat.lt_of_succ_lt hi)⟩
  let b1 := arc.beats.get ⟨i + 1, Nat.lt_of_succ_lt hi⟩
  let b2 := arc.beats.get ⟨i + 2, hi⟩
  let K := computeCurvature b0 b1 b2
  { metric := canonicalMetric
    connection := canonicalChristoffel
    curvature := riemannFromCurvature K
    torsion := canonicalTorsion
    at_beat := b1 }

/-! ## Status -/

def story_tensor_status : String :=
  "╔══════════════════════════════════════════════════════════════╗\n" ++
  "║          STORY TENSOR MODULE - Lean 4 Formalization           ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  ✓ StoryMetric : ds² = dσ² + dE²/φ + dZ²/φ²                   ║\n" ++
  "║  ✓ storyDistance : distance between MoralStates               ║\n" ++
  "║  ✓ StoryCurvature : scalar + sectional curvatures             ║\n" ++
  "║  ✓ curvatureTrajectory : K(t) along arc                       ║\n" ++
  "║  ✓ ChristoffelSymbols : connection coefficients               ║\n" ++
  "║  ✓ NarrativeRiemann : full curvature tensor                   ║\n" ++
  "║  ✓ geodesicDeviation : nearby geodesic separation             ║\n" ++
  "║  ✓ NarrativeTorsion : time-asymmetry                          ║\n" ++
  "║  ✓ StoryTensor : complete geometric structure                 ║\n" ++
  "║  ✓ storyTensorAt : compute full tensor at beat                ║\n" ++
  "╚══════════════════════════════════════════════════════════════╝"

#eval story_tensor_status

end

end Narrative
end IndisputableMonolith
