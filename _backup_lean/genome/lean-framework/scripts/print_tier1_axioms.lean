import IndisputableMonolith.Recognition
import IndisputableMonolith.Cost
import IndisputableMonolith.PhiSupport.Lemmas
import IndisputableMonolith.Patterns
import IndisputableMonolith.Patterns.GrayCycle
import IndisputableMonolith.Verification.Necessity.RecognitionNecessity
import IndisputableMonolith.Verification.Necessity.LedgerNecessity
import IndisputableMonolith.Verification.Dimension
import IndisputableMonolith.Verification.Tier1Cert

/-!
Print axiom dependencies for Tier 1 core theorems.

Run:
  lake env lean scripts/print_tier1_axioms.lean
-/

-- C01
#print axioms IndisputableMonolith.Recognition.mp_holds

-- C02
#print axioms IndisputableMonolith.Verification.Necessity.RecognitionNecessity.observables_require_recognition

-- C03
#print axioms IndisputableMonolith.Verification.Necessity.LedgerNecessity.discrete_forces_ledger

-- C04
#print axioms IndisputableMonolith.Cost.T5_cost_uniqueness_on_pos

-- C05
#print axioms IndisputableMonolith.PhiSupport.phi_unique_pos_root

-- C06
#print axioms IndisputableMonolith.Patterns.cover_exact_pow
#print axioms IndisputableMonolith.Patterns.min_ticks_cover

-- C07
#print axioms IndisputableMonolith.Verification.Dimension.onlyD3_satisfies_RSCounting_Gap45_Absolute

-- Bundle
#print axioms IndisputableMonolith.Verification.Tier1.Tier1Cert.verified_any
