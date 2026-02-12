import Mathlib
import IndisputableMonolith.Octave.Theorem
import IndisputableMonolith.Octave.LedgerBridge
import IndisputableMonolith.Octave.LNALBridge

/-!
# Octave Bundle (canonical import path)

`IndisputableMonolith.Octave.Bundle` is the intended **single import** for the
core octave theorem surface:

- `Octave.Theorem`: phase closure + Gray-8 cover witness in patterns.
- `Octave.LedgerBridge`: posting-step ⇒ parity one-bit adjacency.
- `Octave.LNALBridge`: LNAL Gray-8 schedule agreement + neutrality exports.

This file is intentionally light; it mostly aggregates and re-exports.
-/

namespace IndisputableMonolith
namespace Octave

-- Re-export the most common bridge namespaces for convenience.
export LedgerBridge
  ( postingStep_implies_grayAdj
    postingStep_iff_legalAtomicTick
    legalAtomicTick_implies_grayAdj
    minCost_monotoneStep_implies_postingStep
    postingStep_of_monotone_and_ledgerJlogCost_le_Jlog1
    minJlogCost_monotoneStep_implies_postingStep )
export LNALBridge
  ( lnal_gray8At_eq_patterns_gray8At
    lnal_gray8At_injective
    patterns_grayCycle3Path_eq_lnal_pattern3
    toNat3_grayCycle3Path_eq_lnal_gray8At_val
    neutral_every_8th_from0 )

end Octave
end IndisputableMonolith
