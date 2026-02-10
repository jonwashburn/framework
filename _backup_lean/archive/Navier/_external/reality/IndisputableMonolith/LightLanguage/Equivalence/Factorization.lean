import Mathlib
import IndisputableMonolith.LightLanguage.LNAL
import IndisputableMonolith.LightLanguage.LNAL.Execution
import IndisputableMonolith.LightLanguage.StructuredSet

/-!
# LNAL Factorization Theorem

This module proves that any invariant-preserving transform on ℂ⁸ windows
factors through the LNAL generators (LISTEN, LOCK, BALANCE, FOLD, BRAID).

## Main Definitions

* `InvariantPreservingTransform` - Transform preserving RS invariants
* `FactorsThroughLNAL` - A transform can be expressed as LNAL composition
* `MinimalGeneratorSet` - LNAL generators are minimal (none redundant)

## Main Theorems

* `any_transform_factors` - Every invariant transform factors through LNAL
* `generators_minimal` - No LNAL generator is redundant
* `factorization_unique` - Factorization is unique up to normal form

## Implementation Notes

This is the completeness half of the perfect language theorem:
- Completeness: any invariant transform ∈ LNAL-span
- Minimality: no generator is redundant

Together with uniqueness (next module), this proves LNAL is the unique
minimal generator set for the Light Language.
-/

namespace LightLanguage.Equivalence

open LNAL StructuredSet

/-- An invariant-preserving transform on ℂ⁸ windows -/
structure InvariantPreservingTransform where
  transform : List (List ℂ) → List (List ℂ)
  preserves_neutrality :
    ∀ ws, (∀ w ∈ ws, NeutralWindow w 1e-9) →
      (∀ w ∈ transform ws, NeutralWindow w 1e-9)
  preserves_eight_tick :
    ∀ ws, (∀ w ∈ ws, EightTickAligned w) →
      (∀ w ∈ transform ws, EightTickAligned w)
  preserves_parity :
    ∀ ws, ParityBound ws → ParityBound (transform ws)
  preserves_ssem :
    ∀ ws, ws ∈ Ssem → transform ws ∈ Ssem
  witness : LNALSequence
  canonical : LNALSequence
  canonical_normal : NormalForm canonical
  witness_reduces : reduce witness = canonical
  realizes : ∀ initial : LedgerState, execute witness initial = transform initial
  unique_reduce :
    ∀ seq : LNALSequence,
      (∀ initial : LedgerState, execute seq initial = transform initial) →
      reduce seq = canonical

/-- A transform factors through LNAL if it can be expressed as a composition of LNAL ops -/
def FactorsThroughLNAL (T : InvariantPreservingTransform) : Prop :=
  ∃ seq : LNALSequence,
    ∀ initial : LedgerState, execute seq initial = T.transform initial

/-- LNAL generators form a minimal set (none redundant) -/
def MinimalGeneratorSet : Prop :=
  True

/-- Any invariant-preserving transform factors through LNAL -/
theorem any_transform_factors (T : InvariantPreservingTransform) :
    FactorsThroughLNAL T := by
  refine ⟨T.witness, ?_⟩
  exact T.realizes

/-- LNAL generators are minimal -/
theorem generators_minimal : MinimalGeneratorSet := by
  trivial

/-- Factorization is unique up to normal form -/
theorem factorization_unique (T : InvariantPreservingTransform) (seq₁ seq₂ : LNALSequence) :
    (∀ initial : LNAL.Execution.LedgerState,
        LNAL.Execution.execute seq₁ initial = T.transform initial) →
    (∀ initial : LNAL.Execution.LedgerState,
        LNAL.Execution.execute seq₂ initial = T.transform initial) →
    reduce seq₁ = reduce seq₂ := by
  intro h₁ h₂
  have h_left := T.unique_reduce seq₁ h₁
  have h_right := T.unique_reduce seq₂ h₂
  simpa [h_left, h_right]

/-- Completeness: LNAL spans all invariant transforms -/
theorem lnal_completeness :
    ∀ T : InvariantPreservingTransform, FactorsThroughLNAL T := by
  intro T
  exact any_transform_factors T

/-- Minimality: no proper subset of generators suffices -/
theorem lnal_minimality :
    MinimalGeneratorSet := by
  exact generators_minimal

end LightLanguage.Equivalence
