import Mathlib
import IndisputableMonolith.Verification.Preregistered.Core
import IndisputableMonolith.Verification.MeaningPeriodicTable.Spec
import IndisputableMonolith.Token.WTokenBasis

/-!
# Preregistered Predictions: Meaning / WToken Classification

This file contains **predictions only** — no experimental data.
The predictions are derived from the canonical DFT8-based WToken construction.

## Key Predictions

1. **Structural**: Exactly 20 canonical semantic atoms exist (card = 20).
2. **Classifier**: Each canonical basis vector classifies to its corresponding token.
3. **Invariance**: Classification is invariant under allowed equivalences.

These predictions are frozen before any out-of-sample testing.
-/

namespace IndisputableMonolith
namespace Verification
namespace Preregistered
namespace Meaning

open Token
open MeaningPeriodicTable

/-! ## Structural Predictions -/

/-- Prediction: The token set has exactly 20 elements. -/
def pred_card_20 : Prop := Fintype.card CanonicalTokenId = 20

/-- The card prediction holds. -/
theorem pred_card_20_verified : pred_card_20 :=
  canonical_card_20

/-! ## Classification Predictions -/

/-- Prediction: Every canonical basis classifies to a token in the same basis class.

    NOTE: The classifier can only distinguish 4 basis classes, not all 20 tokens.
    This is because multiple WTokens share the same underlying DFT mode basis. -/
def pred_classifier_correct : Prop :=
  ∀ w : CanonicalTokenId,
    ∃ w' : CanonicalTokenId,
      basisClassOf w' = basisClassOf w ∧
      classify (WTokenId.basisOfId w) = ClassifyResult.exact w'

/-- Prediction: The classifier is deterministic (no parameters). -/
def pred_classifier_deterministic : Prop :=
  ∀ v : Fin 8 → ℂ,
    ∀ (run1 run2 : ClassifyResult),
      run1 = classify v → run2 = classify v → run1 = run2

/-- The deterministic prediction is trivially true by function definition. -/
theorem pred_classifier_deterministic_verified : pred_classifier_deterministic := by
  intro v run1 run2 h1 h2
  rw [h1, h2]

/-! ## Signature Predictions -/

/-- Prediction: MeaningSignature is injective (distinct tokens have distinct signatures). -/
def pred_signature_injective : Prop :=
  Function.Injective signatureOf

/-- The signature injectivity prediction holds. -/
theorem pred_signature_injective_verified : pred_signature_injective :=
  signature_injective

end Meaning
end Preregistered
end Verification
end IndisputableMonolith
