import IndisputableMonolith.Token.WTokenRSLegality
import IndisputableMonolith.Token.WTokenCandidate

/-!
# RS Legality Property Tests

This module provides exhaustive verification tests for the RS legality predicates,
ensuring consistency across the token classification hierarchy.

## Tests Included

1. **Enumeration completeness**: All 20 WTokenIds map to valid RSTokenClassifications
2. **Constraint satisfaction**: Every classification satisfies its tau_constraint
3. **Equivalence consistency**: Roundtrip through all equivalences preserves identity
4. **Cardinality agreement**: All Fintype instances agree on count = 20

## Claim Hygiene

- **THEOREM**: All tests are proved via computation (no sorry/axiom)
- Tests serve as regression guards for the classification infrastructure
-/

namespace IndisputableMonolith
namespace Token
namespace RSLegalityTests

open Water (WTokenMode PhiLevel TauOffset)
open RSTokenClassification

/-! ## Test 1: All WTokenIds produce valid RSTokenClassifications -/

/-- Every WTokenId maps to a valid RSTokenClassification via the equivalence chain. -/
theorem all_ids_have_valid_classification :
    ∀ id : WTokenId, ∃ c : RSTokenClassification, equivWTokenId c = id := by
  intro id
  exact ⟨equivWTokenId.symm id, Equiv.apply_symm_apply _ _⟩

/-- The classification of any WTokenId satisfies the tau_constraint. -/
theorem all_classifications_satisfy_constraint :
    ∀ c : RSTokenClassification, c.family ≠ DFTModeFamily.mode4 → c.tauOffset = 0 :=
  fun c => c.tau_constraint

/-! ## Test 2: Equivalence roundtrips are identity -/

/-- WTokenId → RSTokenClassification → WTokenId is identity. -/
theorem roundtrip_id_classification_id (id : WTokenId) :
    equivWTokenId (equivWTokenId.symm id) = id :=
  Equiv.apply_symm_apply _ _

/-- RSTokenClassification → WTokenId → RSTokenClassification is identity. -/
theorem roundtrip_classification_id_classification (c : RSTokenClassification) :
    equivWTokenId.symm (equivWTokenId c) = c :=
  Equiv.symm_apply_apply _ _

/-- WTokenCandidateParam → RSTokenClassification → WTokenCandidateParam is identity. -/
theorem roundtrip_candidate_classification_candidate (p : WTokenCandidateParam) :
    toWTokenCandidateParam (ofWTokenCandidateParam p) = p :=
  toWTokenCandidateParam_ofWTokenCandidateParam p

/-- RSTokenClassification → WTokenCandidateParam → RSTokenClassification is identity. -/
theorem roundtrip_classification_candidate_classification (c : RSTokenClassification) :
    ofWTokenCandidateParam (toWTokenCandidateParam c) = c :=
  ofWTokenCandidateParam_toWTokenCandidateParam c

/-! ## Test 3: Cardinality agreement across all types -/

/-- WTokenId has exactly 20 elements. -/
theorem wtoken_id_card : Fintype.card WTokenId = 20 := WTokenId.card_eq_20

/-- WTokenCandidateParam has exactly 20 elements. -/
theorem candidate_param_card : Fintype.card WTokenCandidateParam = 20 :=
  WTokenCandidateParam.card_eq_20

/-- RSTokenClassification has exactly 20 elements. -/
theorem rs_classification_card : Fintype.card RSTokenClassification = 20 :=
  RSTokenClassification.card_eq_20

/-- All three types have the same cardinality. -/
theorem all_cards_equal :
    Fintype.card WTokenId = Fintype.card WTokenCandidateParam ∧
    Fintype.card WTokenCandidateParam = Fintype.card RSTokenClassification := by
  constructor
  · rw [wtoken_id_card, candidate_param_card]
  · rw [candidate_param_card, rs_classification_card]

/-! ## Test 4: Mode family coverage -/

/-- All 4 DFT mode families are represented. -/
theorem all_mode_families_covered :
    ∀ f : DFTModeFamily, ∃ c : RSTokenClassification, c.family = f := by
  intro f
  -- Each family appears with level0 and tauOffset 0 (or any valid combo for mode4)
  cases f with
  | mode1 =>
    exact ⟨⟨.mode1, ⟨0, by decide⟩, 0, fun _ => rfl⟩, rfl⟩
  | mode2 =>
    exact ⟨⟨.mode2, ⟨0, by decide⟩, 0, fun _ => rfl⟩, rfl⟩
  | mode3 =>
    exact ⟨⟨.mode3, ⟨0, by decide⟩, 0, fun _ => rfl⟩, rfl⟩
  | mode4 =>
    exact ⟨⟨.mode4, ⟨0, by decide⟩, 0, fun h => absurd rfl h⟩, rfl⟩

/-- All 4 phi levels are represented. -/
theorem all_phi_levels_covered :
    ∀ l : Water.PhiLevel, ∃ c : RSTokenClassification, c.level = phiLevelOfWater l := by
  intro l
  -- Each level appears with mode1 and tauOffset 0
  exact ⟨⟨.mode1, phiLevelOfWater l, 0, fun _ => rfl⟩, rfl⟩

/-! ## Test 5: Tau constraint enforcement -/

/-- Mode1 classifications must have tauOffset = 0. -/
theorem mode1_forces_tau0 (c : RSTokenClassification) (hf : c.family = .mode1) :
    c.tauOffset = 0 := by
  apply c.tau_constraint
  rw [hf]
  decide

/-- Mode2 classifications must have tauOffset = 0. -/
theorem mode2_forces_tau0 (c : RSTokenClassification) (hf : c.family = .mode2) :
    c.tauOffset = 0 := by
  apply c.tau_constraint
  rw [hf]
  decide

/-- Mode3 classifications must have tauOffset = 0. -/
theorem mode3_forces_tau0 (c : RSTokenClassification) (hf : c.family = .mode3) :
    c.tauOffset = 0 := by
  apply c.tau_constraint
  rw [hf]
  decide

/-- Mode4 classifications can have tauOffset = 0 or 1. -/
theorem mode4_allows_both_tau (t : Fin 2) :
    ∃ c : RSTokenClassification, c.family = .mode4 ∧ c.tauOffset = t := by
  fin_cases t
  · exact ⟨⟨.mode4, ⟨0, by decide⟩, 0, fun h => absurd rfl h⟩, rfl, rfl⟩
  · exact ⟨⟨.mode4, ⟨0, by decide⟩, 1, fun h => absurd rfl h⟩, rfl, rfl⟩

/-! ## Summary -/

/-- Test summary: all RS legality tests pass. -/
def test_summary : String :=
  "✓ All 20 WTokenIds map to valid RSTokenClassifications\n" ++
  "✓ All classifications satisfy tau_constraint\n" ++
  "✓ All equivalence roundtrips are identity\n" ++
  "✓ Cardinality = 20 across WTokenId, WTokenCandidateParam, RSTokenClassification\n" ++
  "✓ All 4 mode families covered\n" ++
  "✓ All 4 phi levels covered\n" ++
  "✓ Tau constraint correctly enforced per mode family\n" ++
  "\nRS LEGALITY TESTS: ALL PASSED"

#eval test_summary

end RSLegalityTests
end Token
end IndisputableMonolith
