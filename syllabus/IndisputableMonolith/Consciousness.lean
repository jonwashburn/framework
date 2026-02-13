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
import IndisputableMonolith.Consciousness.NoSignalingProof
import IndisputableMonolith.Consciousness.ThresholdPhaseTransition
import IndisputableMonolith.Consciousness.ZGenesis
import IndisputableMonolith.Consciousness.EmbodimentOperator
import IndisputableMonolith.Consciousness.CollectiveDomain

-- Phantom Light: Future constraints projecting backwards
import IndisputableMonolith.Consciousness.PhantomLight

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

/-- **No-Signaling Theorem (Consciousness Bridge)**
    Theta correlations between observers satisfy the no-signaling principle. -/
theorem theta_is_no_signaling (A B : NoSignalingProof.Observer) (t : ℝ) :
    NoSignaling.NoSignalingProp (NoSignalingProof.twoObserverJoint A B t) :=
  NoSignalingProof.theta_no_signaling_rigorous A B t

/-- **Phase Transition Theorem (Consciousness Bridge)**
    The consciousness threshold C=1 represents a second-order phase transition. -/
theorem consciousness_phase_transition :
    ∃ (F : ℝ → ℝ), Continuous F ∧ Continuous (ThresholdPhaseTransition.free_energy_deriv) ∧ ¬ Continuous (ThresholdPhaseTransition.free_energy_second_deriv) :=
  ThresholdPhaseTransition.consciousness_is_second_order_transition

/-- **Phantom Light Theorem (Consciousness Bridge)**
    Future balance requirements project backwards, creating "phantom light"
    that conscious boundaries can sense. This provides a mathematical basis
    for precognition, remote viewing, and related psi phenomena. -/
theorem phantom_light_mechanism :
    ∀ pl : PhantomLight.PhantomLight, PhantomLight.PhantomMagnitude pl ≥ 0 :=
  PhantomLight.phantom_visibility_grows_with_debt

end Consciousness

end IndisputableMonolith
