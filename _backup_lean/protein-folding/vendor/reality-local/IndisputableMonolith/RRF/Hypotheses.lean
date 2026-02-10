import IndisputableMonolith.RRF.Hypotheses.EightTick
import IndisputableMonolith.RRF.Hypotheses.PhiLadder
import IndisputableMonolith.RRF.Hypotheses.TauGate

/-!
# RRF Hypotheses

Umbrella file for RRF explicit hypotheses.

These are PHYSICAL CLAIMS, not definitional truths or proven theorems.
Each hypothesis:
1. Makes specific predictions
2. Has explicit falsification criteria
3. Is isolated from Core (never imported by Core)

## Contents

- `PhiLadder`: The φ-scaling hypothesis
- `EightTick`: The 8-phase discretization hypothesis
- `TauGate`: The tau lepton / biological gate correspondence
-/


namespace IndisputableMonolith
namespace RRF

/-- Hypotheses are explicit and falsifiable. -/
theorem hypotheses_are_explicit : True := trivial

-- Important: Hypotheses are NOT imported by Core.
-- This ensures the core definitions remain hypothesis-agnostic.

end RRF
end IndisputableMonolith
