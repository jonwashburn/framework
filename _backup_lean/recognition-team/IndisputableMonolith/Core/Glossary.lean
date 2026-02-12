import IndisputableMonolith.RRF.Core.DisplayChannel
import IndisputableMonolith.RRF.Core.Octave
import IndisputableMonolith.RRF.Core.Strain
import IndisputableMonolith.RRF.Core.Vantage

/-!
# RRF Core: Glossary

Official symbols and canonical terminology for the Reality Recognition Framework.

This file serves as the single source of truth for RRF vocabulary.
All other modules should use these names consistently.

## Key Symbols

| Symbol | Lean Name | Meaning |
|--------|-----------|---------|
| J | `StrainFunctional.J` | Strain/cost functional |
| V | `Vantage` | {inside, act, outside} |
| R | `Recognize` | Recognition pairing |
| O | `Octave` | A scale of manifestation |
| C | `DisplayChannel` | Observation channel |
| L | `LedgerConstraint` | Double-entry constraint |
| φ | (Hypotheses only) | Golden ratio scaling |
| τ | (Hypotheses only) | Base timescale |

## Terminology

- **Recognition**: The fundamental act by which distinctions become actual
- **Vantage**: One of three perspectives {inside, act, outside}
- **Strain**: Deviation from balance (J → 0 is the law)
- **Octave**: A scale/level of manifestation
- **Display Channel**: A way of observing states
- **Ledger**: Conservation accounting (debit = credit)
-/


namespace IndisputableMonolith
namespace RRF.Core

/-! ## Canonical Type Aliases -/

/-- J: The strain/cost of a state. -/
abbrev J {State : Type*} (S : StrainFunctional State) := S.J

/-- V: The vantage type. -/
abbrev V := Vantage

/-- isBalanced: Zero-strain predicate. -/
abbrev isBalanced {State : Type*} := StrainFunctional.isBalanced (State := State)

/-- isMinimizer: Strain minimizer predicate. -/
abbrev isMinimizer {State : Type*} := StrainFunctional.isMinimizer (State := State)

/-! ## Key Properties (as propositions) -/

/-- The "J → 0" law: strain minimization is the fundamental drive. -/
def JMinimizationLaw {State : Type*} (S : StrainFunctional State) : Prop :=
  ∃ x, S.isBalanced x

/-- Ledger closure: the double-entry constraint holds. -/
def LedgerClosure {State : Type*} (L : LedgerConstraint State) (x : State) : Prop :=
  L.isClosed x

/-- Channel equivalence: two channels induce the same state ordering. -/
abbrev ChannelEquiv {State Obs₁ Obs₂ : Type*} :=
  QualityEquiv (State := State) (Obs₁ := Obs₁) (Obs₂ := Obs₂)

/-! ## RRF Consistency Conditions

For a state to be "real" (recognized), it must satisfy:
1. Strain minimization (or at least local minimum)
2. Ledger closure
3. Consistent observation across channels
-/

/-- A state is RRF-consistent if it has low strain and closed ledger. -/
def isConsistent {State : Type*}
    (SL : StrainLedger State) (x : State) : Prop :=
  SL.strain.isBalanced x ∧ SL.ledger.isClosed x

/-- The set of RRF-consistent states. -/
def consistentStates {State : Type*} (SL : StrainLedger State) : Set State :=
  { x | isConsistent SL x }

end RRF.Core
end IndisputableMonolith
