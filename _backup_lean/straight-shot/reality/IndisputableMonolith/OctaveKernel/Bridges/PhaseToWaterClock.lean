import IndisputableMonolith.OctaveKernel.Bridges.PhaseHub
import IndisputableMonolith.OctaveKernel.Instances.WaterClockLayer

namespace IndisputableMonolith
namespace OctaveKernel
namespace Bridges

open IndisputableMonolith.OctaveKernel.Instances

/-!
# OctaveKernel.Bridges.PhaseToWaterClock

A first **concrete** cross-layer bridge: from the canonical `PhaseLayer` to the
BIOPHASE `WaterClockLayer`.

This bridge is intentionally conservative:
- It does **not** claim any physical identification from phase alone.
- It simply embeds a phase into a canonical, admissible water-clock observation state.

This gives us a typed arrow `PhaseLayer → WaterClockLayer` that preserves phase
and commutes with stepping (both are mod-8).
-/

/-- A canonical water-clock observation state for a given phase.

We pick boundary values that satisfy the acceptance predicate:
- `snr = 5`, `correlation = 0.30`, `circVariance = 0.40`.
-/
def waterOfPhase (p : Phase) : WaterClockState :=
{ bandIndex := p
, snr := 5
, correlation := 0.30
, circVariance := 0.40
}

lemma waterOfPhase_admissible (p : Phase) :
    WaterClockState.passesAcceptance (waterOfPhase p) := by
  simp [waterOfPhase, WaterClockState.passesAcceptance]

/-- A bridge from the canonical phase layer into the water clock layer. -/
noncomputable def phaseToWaterClockBridge : Bridge PhaseLayer WaterClockLayer :=
{ map := waterOfPhase
, preservesPhase := by
    intro p
    rfl
, commutesStep := by
    intro p
    -- Both steps advance the `bandIndex` by 1 mod 8; all other fields are constant.
    simp [PhaseLayer, WaterClockLayer, waterOfPhase, WaterClockState.advance]
}

end Bridges
end OctaveKernel
end IndisputableMonolith
