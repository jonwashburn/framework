import IndisputableMonolith.OctaveKernel.Bridges.PhaseHub
import IndisputableMonolith.OctaveKernel.Bridges.PhaseToWaterClock
import IndisputableMonolith.OctaveKernel.Bridges.WaterClockToPhase
import IndisputableMonolith.OctaveKernel.Instances.PatternCover

namespace IndisputableMonolith
namespace OctaveKernel
namespace Bridges

open IndisputableMonolith.OctaveKernel.Instances

/-!
# OctaveKernel.Bridges.PhaseToPatternCover

This module builds conservative bridges between:

- the canonical `PhaseLayer` (phase-only hub), and
- `Instances.PatternCoverLayer` (the 8-beat witness backed by `Patterns`).

Since both layers have `State = Fin 8` and `step = (+1)`, these bridges are essentially
identity maps on the underlying phase.

We also expose derived bridges between `PatternCoverLayer` and `WaterClockLayer` by composing
existing bridges through `PhaseLayer`.
-/

/-! ## PhaseLayer ↔ PatternCoverLayer -/

/-- Bridge `PhaseLayer → PatternCoverLayer` (identity on `Fin 8`). -/
noncomputable def phaseToPatternCoverBridge : Bridge PhaseLayer PatternCoverLayer :=
{ map := fun p => p
, preservesPhase := by
    intro _p
    rfl
, commutesStep := by
    intro _p
    rfl
}

/-- Bridge `PatternCoverLayer → PhaseLayer` (identity on `Fin 8`). -/
noncomputable def patternCoverToPhaseBridge : Bridge PatternCoverLayer PhaseLayer :=
{ map := fun p => p
, preservesPhase := by
    intro _p
    rfl
, commutesStep := by
    intro _p
    rfl
}

/-! ## Derived bridges: PatternCover ↔ WaterClock (via PhaseLayer) -/

/-- Bridge `PatternCoverLayer → WaterClockLayer` obtained by composition through `PhaseLayer`. -/
noncomputable def patternCoverToWaterClockBridge : Bridge PatternCoverLayer WaterClockLayer :=
  Bridge.comp patternCoverToPhaseBridge phaseToWaterClockBridge

/-- Bridge `WaterClockLayer → PatternCoverLayer` obtained by composition through `PhaseLayer`. -/
noncomputable def waterClockToPatternCoverBridge : Bridge WaterClockLayer PatternCoverLayer :=
  Bridge.comp waterClockToPhaseBridge phaseToPatternCoverBridge

/-- Roundtrip: PatternCover → WaterClock → PatternCover is the identity on phases. -/
theorem pattern_water_roundtrip (p : Phase) :
    waterClockToPatternCoverBridge.map (patternCoverToWaterClockBridge.map p) = p := by
  -- Unfold the composed maps; reduces to the existing phase roundtrip lemma.
  rfl

end Bridges
end OctaveKernel
end IndisputableMonolith
