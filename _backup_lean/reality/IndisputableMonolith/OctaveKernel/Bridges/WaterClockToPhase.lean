import IndisputableMonolith.OctaveKernel.Bridges.PhaseHub
import IndisputableMonolith.OctaveKernel.Bridges.PhaseToWaterClock
import IndisputableMonolith.OctaveKernel.Instances.WaterClockLayer

namespace IndisputableMonolith
namespace OctaveKernel
namespace Bridges

open IndisputableMonolith.OctaveKernel.Instances

/-!
# OctaveKernel.Bridges.WaterClockToPhase

A conservative bridge back from the BIOPHASE `WaterClockLayer` to the canonical `PhaseLayer`.

This is a purely structural bridge:
- It projects a water-clock state to its `bandIndex : Fin 8`.
- It preserves phase and commutes with step.

We also record a simple **roundtrip** lemma showing that the embedding
`PhaseLayer → WaterClockLayer` (from `PhaseToWaterClock`) followed by this projection
returns the original phase.
-/

/-- Project a water-clock state to its phase (band index). -/
def phaseOfWater (s : WaterClockState) : Phase :=
  s.bandIndex

/-- Bridge from `WaterClockLayer` to the canonical `PhaseLayer` via phase projection. -/
noncomputable def waterClockToPhaseBridge : Bridge WaterClockLayer PhaseLayer :=
  phaseProjectionBridge WaterClockLayer Instances.WaterClockLayer_stepAdvances

theorem waterClockToPhase_surjective : Function.Surjective waterClockToPhaseBridge.map := by
  intro p
  refine ⟨waterOfPhase p, ?_⟩
  rfl

/-- Roundtrip: projecting the canonical water-state for a phase returns that phase. -/
theorem phase_roundtrip (p : Phase) :
    waterClockToPhaseBridge.map (phaseToWaterClockBridge.map p) = p := by
  rfl

/-- Roundtrip (general): for any `StepAdvances` layer, projecting to `PhaseLayer`,
embedding into `WaterClockLayer`, then projecting back returns the same phase. -/
theorem phase_roundtrip_of_projection (L : Layer) (hAdv : Layer.StepAdvances L) (s : L.State) :
    waterClockToPhaseBridge.map (phaseToWaterClockBridge.map ((phaseProjectionBridge L hAdv).map s)) =
      (phaseProjectionBridge L hAdv).map s := by
  simpa using phase_roundtrip ((phaseProjectionBridge L hAdv).map s)

end Bridges
end OctaveKernel
end IndisputableMonolith
