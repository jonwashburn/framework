import IndisputableMonolith.OctaveKernel.Bridges.PhaseHub
import IndisputableMonolith.OctaveKernel.Bridges.PhaseToWaterClock
import IndisputableMonolith.OctaveKernel.Bridges.PhaseToPatternCover
import IndisputableMonolith.OctaveKernel.Instances.BiologyLayer
import IndisputableMonolith.OctaveKernel.Instances.ConsciousnessLayer
import IndisputableMonolith.OctaveKernel.Instances.LNALAligned
import IndisputableMonolith.OctaveKernel.Instances.MeaningNoteLayer
import IndisputableMonolith.OctaveKernel.Instances.PhysicsScaleLayer

namespace IndisputableMonolith
namespace OctaveKernel
namespace Bridges

open IndisputableMonolith.OctaveKernel.Instances

/-!
# OctaveKernel.Bridges.LayerProjections

This module defines **named projection bridges** from domain witness layers into the
canonical `PhaseLayer`, and then derives “to-water” / “to-pattern” bridges by
composition through the hub.

These bridges are intentionally conservative: they move only *phase* information.
-/

/-! ## Projections to PhaseLayer -/

/-- Biology (Q₆ witness) → Phase hub. -/
noncomputable def biologyToPhaseBridge : Bridge BiologyQualiaLayer PhaseLayer :=
  phaseProjectionBridge BiologyQualiaLayer BiologyQualiaLayer_stepAdvances

/-- Consciousness (Θ witness) → Phase hub. -/
noncomputable def consciousnessToPhaseBridge : Bridge ConsciousnessPhaseLayer PhaseLayer :=
  phaseProjectionBridge ConsciousnessPhaseLayer ConsciousnessPhaseLayer_stepAdvances

/-- Meaning (LNAL breath%8 witness) → Phase hub. -/
noncomputable def lnalToPhaseBridge (P : LNAL.LProgram) : Bridge (LNALBreathLayer P) PhaseLayer :=
  phaseProjectionBridge (LNALBreathLayer P) (LNALBreathLayer_stepAdvances P)

/-- MeaningNote (WTokens↔AA↔Codon witness) → Phase hub. -/
noncomputable def meaningNoteToPhaseBridge : Bridge MeaningNoteLayer PhaseLayer :=
  phaseProjectionBridge MeaningNoteLayer MeaningNoteLayer_stepAdvances

/-! ## Derived bridges via the hub -/

-- Phase hub → Water clock is already provided as `phaseToWaterClockBridge`.

/-- Biology → Water clock (via Phase hub). -/
noncomputable def biologyToWaterClockBridge : Bridge BiologyQualiaLayer WaterClockLayer :=
  Bridge.comp biologyToPhaseBridge phaseToWaterClockBridge

/-- Consciousness → Water clock (via Phase hub). -/
noncomputable def consciousnessToWaterClockBridge : Bridge ConsciousnessPhaseLayer WaterClockLayer :=
  Bridge.comp consciousnessToPhaseBridge phaseToWaterClockBridge

/-- LNAL → Water clock (via Phase hub). -/
noncomputable def lnalToWaterClockBridge (P : LNAL.LProgram) : Bridge (LNALBreathLayer P) WaterClockLayer :=
  Bridge.comp (lnalToPhaseBridge P) phaseToWaterClockBridge

/-- MeaningNote → Water clock (via Phase hub). -/
noncomputable def meaningNoteToWaterClockBridge : Bridge MeaningNoteLayer WaterClockLayer :=
  Bridge.comp meaningNoteToPhaseBridge phaseToWaterClockBridge

-- Phase hub → PatternCover is provided as `phaseToPatternCoverBridge`.

/-- Biology → PatternCover (via Phase hub). -/
noncomputable def biologyToPatternCoverBridge : Bridge BiologyQualiaLayer PatternCoverLayer :=
  Bridge.comp biologyToPhaseBridge phaseToPatternCoverBridge

/-- Consciousness → PatternCover (via Phase hub). -/
noncomputable def consciousnessToPatternCoverBridge : Bridge ConsciousnessPhaseLayer PatternCoverLayer :=
  Bridge.comp consciousnessToPhaseBridge phaseToPatternCoverBridge

/-- LNAL → PatternCover (via Phase hub). -/
noncomputable def lnalToPatternCoverBridge (P : LNAL.LProgram) : Bridge (LNALBreathLayer P) PatternCoverLayer :=
  Bridge.comp (lnalToPhaseBridge P) phaseToPatternCoverBridge

/-- MeaningNote → PatternCover (via Phase hub). -/
noncomputable def meaningNoteToPatternCoverBridge : Bridge MeaningNoteLayer PatternCoverLayer :=
  Bridge.comp meaningNoteToPhaseBridge phaseToPatternCoverBridge

/-! ## Physics layer bridges -/

/-- Physics (φ-ladder witness) → Phase hub. -/
noncomputable def physicsToPhaseBridge : Bridge PhysicsScaleLayer PhaseLayer :=
  phaseProjectionBridge PhysicsScaleLayer PhysicsScaleLayer_stepAdvances

/-- Physics → Water clock (via Phase hub). -/
noncomputable def physicsToWaterClockBridge : Bridge PhysicsScaleLayer WaterClockLayer :=
  Bridge.comp physicsToPhaseBridge phaseToWaterClockBridge

/-- Physics → PatternCover (via Phase hub). -/
noncomputable def physicsToPatternCoverBridge : Bridge PhysicsScaleLayer PatternCoverLayer :=
  Bridge.comp physicsToPhaseBridge phaseToPatternCoverBridge

end Bridges
end OctaveKernel
end IndisputableMonolith
