import IndisputableMonolith.OctaveKernel.Instances.PatternCover
import IndisputableMonolith.OctaveKernel.Instances.LNALAligned
import IndisputableMonolith.OctaveKernel.Instances.BiologyLayer
import IndisputableMonolith.OctaveKernel.Instances.WaterClockLayer
import IndisputableMonolith.OctaveKernel.Instances.ConsciousnessLayer
import IndisputableMonolith.OctaveKernel.Instances.MeaningNoteLayer
import IndisputableMonolith.OctaveKernel.Instances.PhysicsScaleLayer

/-!
# IndisputableMonolith.OctaveKernel.Instances

Umbrella imports for small, conservative "instance witnesses" that connect
existing Monolith modules to the `OctaveKernel` interface.

These instances are **not** claims about nature; they are packaging layers
that make it easier to state and prove cross-domain invariance theorems.

## Available Instances

- **PatternCoverLayer**: 8-beat structure from `Patterns.lean` (period_exactly_8)
- **LNALBreathLayer**: LNAL VM breath clock mod 8 (meaning layer)
- **BiologyQualiaLayer**: Q₆ trajectory walker (biology/folding layer)
- **WaterClockLayer**: BIOPHASE 724 cm⁻¹ 8-band structure (water/clock layer)
- **ConsciousnessPhaseLayer**: Global phase Θ + 45-tick mind clock (consciousness layer)
- **PhysicsScaleLayer**: φ-ladder scale algebra (physics layer)
-/
