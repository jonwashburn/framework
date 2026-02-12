import IndisputableMonolith.OctaveKernel.Bridges.Basic
import IndisputableMonolith.OctaveKernel.Bridges.PhaseHub
import IndisputableMonolith.OctaveKernel.Bridges.PhaseToWaterClock
import IndisputableMonolith.OctaveKernel.Bridges.WaterClockToPhase
import IndisputableMonolith.OctaveKernel.Bridges.PhaseToPatternCover
import IndisputableMonolith.OctaveKernel.Bridges.LayerProjections
import IndisputableMonolith.OctaveKernel.Bridges.AlignmentTheorems

/-!
# IndisputableMonolith.OctaveKernel.Bridges

Umbrella import for bridge definitions and conservative bridge constructions.

Guiding principle:
- Bridges should be **typed** and **claim-hygienic**.
- Purely mathematical/structural bridges belong here.
- Empirical identifications should remain hypotheses with explicit falsifiers.
-/
