import Mathlib
import IndisputableMonolith.Verification.Preregistered.Meaning.Prediction
import IndisputableMonolith.Verification.Preregistered.Meaning.AminoAcidCorrespondence

/-!
# Preregistered Tests: Meaning / WToken Classification

This file imports predictions and tests them.
Tests are structured as theorem statements that connect predictions to verified facts.

## Test Status

| Test | Status |
|------|--------|
| Card = 20 | PASS (theorem) |
| Signature injective | PASS (theorem) |
| Classifier deterministic | PASS (theorem) |
| Classifier correct | HYPOTHESIS (requires orthogonality proofs) |
| Amino acid count match | PASS (theorem) |
| Amino acid isomorphism | PASS (theorem) |
| Codon reduction | PASS (theorem) |
-/

namespace IndisputableMonolith
namespace Verification
namespace Preregistered
namespace Meaning

open MeaningPeriodicTable

/-! ## Passing Tests (THEOREM-backed) -/

/-- Test: Cardinality prediction passes. -/
theorem test_card_20_passes : pred_card_20 :=
  pred_card_20_verified

/-- Test: Signature injectivity prediction passes. -/
theorem test_signature_injective_passes : pred_signature_injective :=
  pred_signature_injective_verified

/-- Test: Classifier determinism prediction passes. -/
theorem test_classifier_deterministic_passes : pred_classifier_deterministic :=
  pred_classifier_deterministic_verified

/-! ## Pending Tests (require more infrastructure) -/

/-- Test: Classifier correctness.
    Status: HYPOTHESIS — proof requires DFT8 mode orthogonality lemmas.

    The statement is: every canonical basis vector classifies to its token.
    This follows from:
    1. basisOfId w is already neutral (basisOfId_neutral)
    2. basisOfId w has unit norm (basisOfId_normalized)
    3. Inner product with itself is 1
    4. Inner product with other modes is 0 (orthogonality)
    5. Therefore maxOverlapToken returns w

    Full proof is deferred pending orthogonality infrastructure. -/
theorem test_classifier_correct_passes : pred_classifier_correct :=
  classify_correct

/-! ## Amino Acid Correspondence Tests -/

/-- Test: Amino acid count matches WToken count. -/
theorem test_amino_acid_count_passes : AminoAcid.pred_count_match :=
  AminoAcid.test_count_match_passes

/-- Test: Amino acid isomorphism exists. -/
theorem test_amino_acid_isomorphism_passes : AminoAcid.pred_isomorphism_exists :=
  AminoAcid.test_isomorphism_exists_passes

/-- Test: Codon reduction exists. -/
theorem test_codon_reduction_passes : AminoAcid.pred_codon_reduction :=
  AminoAcid.test_codon_reduction_passes

/-! ## Summary -/

/-- All structural predictions pass. -/
theorem meaning_structural_tests_pass :
    pred_card_20 ∧ pred_signature_injective ∧ pred_classifier_deterministic :=
  ⟨pred_card_20_verified, pred_signature_injective_verified, pred_classifier_deterministic_verified⟩

/-- All amino acid correspondence predictions pass. -/
theorem meaning_amino_acid_tests_pass :
    AminoAcid.pred_count_match ∧ AminoAcid.pred_isomorphism_exists ∧ AminoAcid.pred_codon_reduction :=
  AminoAcid.amino_acid_correspondence_tests_pass

/-- Master summary: All meaning tests that currently pass. -/
theorem meaning_all_passing_tests :
    pred_card_20 ∧ pred_signature_injective ∧ pred_classifier_deterministic ∧
    AminoAcid.pred_count_match ∧ AminoAcid.pred_isomorphism_exists ∧ AminoAcid.pred_codon_reduction :=
  ⟨pred_card_20_verified, pred_signature_injective_verified, pred_classifier_deterministic_verified,
   AminoAcid.test_count_match_passes, AminoAcid.test_isomorphism_exists_passes,
   AminoAcid.test_codon_reduction_passes⟩

end Meaning
end Preregistered
end Verification
end IndisputableMonolith
