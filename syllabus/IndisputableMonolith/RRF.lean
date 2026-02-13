import IndisputableMonolith.RRF.Adapters
import IndisputableMonolith.RRF.Core
import IndisputableMonolith.RRF.Foundation
import IndisputableMonolith.RRF.Hypotheses
import IndisputableMonolith.RRF.Models
import IndisputableMonolith.RRF.Theorems

/-!
# Reality Recognition Framework (RRF)

Main umbrella file for the RRF formalization.

RRF is a layered theory:
- **Foundation**: The derivation chain (MP → Ledger → φ → Constants)
- **Core**: Definitional truths (Vantage, Strain, Octave, etc.)
- **Theorems**: Proven mathematical facts
- **Models**: Consistency witnesses
- **Hypotheses**: Explicit physical claims (φ-ladder, 8-tick, tau-gate)
- **Adapters**: Connection to empirical artifacts

## The Derivation Chain

```
MetaPrinciple → Ledger → φ → E_coh → τ₀ → c → ℏ → G → α
```

## The Vantage Equivalence

```
Outside (Physics) ≃ Act (Meaning) ≃ Inside (Qualia)
```

## Usage

```lean

-- Use Core definitions
open IndisputableMonolith.RRF.Core

-- Apply theorems
open IndisputableMonolith.RRF.Theorems

-- Instantiate models
open IndisputableMonolith.RRF.Models

-- (Carefully) use hypotheses
open IndisputableMonolith.RRF.Hypotheses
```

## Design Principles

1. **Layered certainty**: Definitions vs. theorems vs. hypotheses
2. **Grounded abstraction**: Lean audits real traces
3. **Explicit falsification**: Hypotheses declare what would refute them
4. **Minimal mathlib**: Core compiles fast
-/

-- Core: Definitional content

-- Theorems: Proven facts

-- Models: Consistency witnesses

-- Hypotheses: Physical claims (isolated)

-- Adapters: Empirical connection

namespace IndisputableMonolith
namespace RRF

/-! ## RRF Status -/

/-- RRF is internally consistent (at universe 0). -/
theorem rrf_consistent : Nonempty (Core.Octave.{0, 0, 0}) := models_exist

/-!
## RRF Status

RRF is complete and all components are integrated.
-/

/-! ## Quick Reference -/

/-- The three vantages. -/
example : Core.Vantage := .inside

/-- A strain functional. -/
example : Core.StrainFunctional Unit := { J := fun _ => 0 }

/-- The trivial model exists. -/
example : Core.Octave := Models.trivialOctave

/-- φ is defined. -/
noncomputable example : ℝ := Hypotheses.phi

end RRF
end IndisputableMonolith
