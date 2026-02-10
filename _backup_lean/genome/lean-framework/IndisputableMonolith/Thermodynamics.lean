import IndisputableMonolith.Thermodynamics.RecognitionThermodynamics
import IndisputableMonolith.Thermodynamics.MaxEntFromCost
import IndisputableMonolith.Thermodynamics.FreeEnergyMonotone
import IndisputableMonolith.Thermodynamics.ErrorCorrection
import IndisputableMonolith.Thermodynamics.PhaseTransitions
import IndisputableMonolith.Thermodynamics.MemoryLedger

/-!
# Recognition Thermodynamics

This module develops the statistical mechanics of Recognition Science (RS).

## Overview

Recognition Science has established a "T=0" foundation where reality is defined by
the absolute minimization of a universal cost functional J(x) = ½(x + 1/x) - 1.
This module extends RS to finite Recognition Temperature (TR), enabling:

1. **Noise and Fluctuations**: Understanding "almost-stable" states
2. **Learning and Exploration**: The exploration-exploitation tradeoff
3. **Arrow of Time**: Global relaxation toward low free energy
4. **Error Correction**: Fault tolerance as the origin of physical law stability
5. **Memory Dynamics**: Retention vs. free-energy decay

## Submodules

- `RecognitionThermodynamics`: Core definitions (TR, β, Gibbs measure, SR, FR)
- `MaxEntFromCost`: Gibbs minimizes free energy, maximizes entropy for fixed cost
- `FreeEnergyMonotone`: Second Law of Recognition (dFR/dt ≤ 0)
- `ErrorCorrection`: Error correction viewpoint, fault tolerance thresholds
- `PhaseTransitions`: Critical phenomena, coherence threshold C=1
- `MemoryLedger`: Memory as thermodynamic system (Priority #6 from RS_UNDISCOVERED_TERRITORIES)

## Key Concepts

### Recognition Temperature (TR)
Parameterizes the strictness of J-minimization:
- TR = 0: Deterministic RS (only J=0 states exist)
- TR = T_φ = ln(φ): Critical point (C=1 coherence threshold)
- TR → ∞: Maximum disorder (uniform distribution)

### Recognition Free Energy (FR)
The fundamental variational quantity:
  FR(p) := E_p[J] - TR × SR(p)

The Gibbs measure minimizes FR:
  p_G(x) ∝ exp(-J(x)/TR)

### Arrow of Time
Time flows in the direction of decreasing FR:
  dFR/dt ≤ 0

This unifies:
- Thermodynamic arrow (entropy increase)
- Cosmological arrow (universe expansion toward equilibrium)
- Psychological arrow (learning, adaptation)

## References

- RS_UNDISCOVERED_TERRITORIES.md
- Recognition-Science-Full-Theory.txt
- Statistical Mechanics of Recognition (paper draft)
-/
