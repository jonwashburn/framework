/-!
# Project Helios – RS Fusion Formalization Bundle

This is the Lean 4 formalization bundle for recognition-science coherence-controlled fusion,
extracted from the IndisputableMonolith repository.

## Core Certificate Theorem

The primary result is the viability threshold certificate:

  `viable_of_T_ge_T_star_and_E_ge_E_star`

in `IndisputableMonolith/Fusion/ViabilityThresholds.lean`.

## Replay Command

```bash
lake exe cache get          # fetch Mathlib cache (one-time, ~2GB)
lake build IndisputableMonolith.Fusion.ViabilityThresholds
```

## File Index

### Viability Certificate (primary)
- `Fusion/ViabilityThresholds.lean` – solvable thresholds T*, E* and main theorem
- `Fusion/PowerBalanceBounds.lean` – concrete inequality bounds
- `Fusion/PowerBalance.lean` – loss and heating models
- `Fusion/ReactivityProxy.lean` – reactivity proxy ⟨σv⟩(T)
- `Fusion/Ignition.lean` – viability/ignition predicates

### Nuclear Bridge
- `Fusion/ReactionNetworkRates.lean` – Gamow exponent and tunneling
- `Fusion/ReactionNetwork.lean` – fusion reaction network
- `Fusion/NuclearBridge.lean` – nuclear configuration interface
- `Fusion/BindingEnergy.lean` – binding energy model

### Coherence Control
- `Fusion/SymmetryLedger.lean` – J-cost symmetry ledger
- `Fusion/SymmetryProxy.lean` – symmetry proxy
- `Fusion/Scheduler.lean` – φ-spaced pulse scheduling
- `Fusion/Certificate.lean` – certificate bundles

### Foundations
- `Constants.lean` – RS-native constants (φ, τ₀, etc.)
- `Cost.lean` – J-cost function
- `Nuclear/MagicNumbers.lean` – magic number formalization
-/

-- Primary certificate module
import IndisputableMonolith.Fusion.ViabilityThresholds

-- Supporting fusion modules
import IndisputableMonolith.Fusion.PowerBalanceBounds
import IndisputableMonolith.Fusion.PowerBalance
import IndisputableMonolith.Fusion.ReactivityProxy
import IndisputableMonolith.Fusion.Ignition
import IndisputableMonolith.Fusion.ReactionNetworkRates
import IndisputableMonolith.Fusion.ReactionNetwork
import IndisputableMonolith.Fusion.NuclearBridge
import IndisputableMonolith.Fusion.BindingEnergy
import IndisputableMonolith.Fusion.SymmetryLedger
import IndisputableMonolith.Fusion.SymmetryProxy
import IndisputableMonolith.Fusion.Scheduler
import IndisputableMonolith.Fusion.Certificate
import IndisputableMonolith.Fusion.Executable.Interfaces

-- Foundations
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
import IndisputableMonolith.Nuclear.MagicNumbers
