import IndisputableMonolith.Consciousness.ConsciousProcess
import IndisputableMonolith.Consciousness.PhotonChannel
import IndisputableMonolith.Consciousness.NoMediumKnobs
import IndisputableMonolith.Consciousness.NullOnly
import IndisputableMonolith.Consciousness.Maxwellization
import IndisputableMonolith.Consciousness.BioPhaseSNR
-- import IndisputableMonolith.Consciousness.Equivalence -- TODO: fix type-class instance calls
import IndisputableMonolith.Consciousness.ConsciousnessHamiltonian
import IndisputableMonolith.Consciousness.GlobalPhase
import IndisputableMonolith.Consciousness.ThetaDynamics
import IndisputableMonolith.Consciousness.RecognitionBinding
import IndisputableMonolith.Consciousness.RecognitionMemory
import IndisputableMonolith.Consciousness.CollapseSelection
import IndisputableMonolith.Consciousness.PatternPersistence
import IndisputableMonolith.Consciousness.LightMemory
import IndisputableMonolith.Consciousness.PhaseSaturation
import IndisputableMonolith.Consciousness.SubstrateSuitability
import IndisputableMonolith.Consciousness.ResurrectionOperator
import IndisputableMonolith.Consciousness.Recurrence
import IndisputableMonolith.Consciousness.Timing

-- Θ / soul "missing module" spine (scaffolds)
import IndisputableMonolith.Consciousness.ThetaModes
import IndisputableMonolith.Consciousness.ThetaThermodynamics
import IndisputableMonolith.Consciousness.ThetaTransport
import IndisputableMonolith.Consciousness.ThetaDefects
import IndisputableMonolith.Consciousness.NoSignaling
import IndisputableMonolith.Consciousness.ThetaNoSignaling
import IndisputableMonolith.Consciousness.ZGenesis
import IndisputableMonolith.Consciousness.EmbodimentOperator
import IndisputableMonolith.Consciousness.CollectiveDomain

/-!
# Consciousness Module Aggregator

This module aggregates all consciousness-related definitions and theorems,
providing the complete framework for the Light = Consciousness bi-interpretability
theorem.

**Structure**:
- `ConsciousProcess`: Bridge-side operational definition
- `PhotonChannel`: Maxwell/DEC electromagnetic channel
- `NoMediumKnobs` (Lemma A): Excludes material-dependent channels
- `NullOnly` (Lemma B): Forces null propagation
- `Maxwellization` (Lemma C): Classifies to U(1) gauge theory
- `BioPhaseSNR` (Lemma D): BIOPHASE acceptance selects EM
- `Equivalence`: Main bi-interpretability theorem

**Usage**:
```lean
import IndisputableMonolith.Consciousness

open IndisputableMonolith.Consciousness

-- Access definitions
#check ConsciousProcess
#check PhotonChannel
#check light_equals_consciousness
```
-/

namespace IndisputableMonolith

-- Re-export main namespaces
namespace Consciousness
end Consciousness

end IndisputableMonolith
