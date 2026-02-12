import Mathlib
import IndisputableMonolith.Constants.KDisplay
import IndisputableMonolith.RH.RS.Spec
import IndisputableMonolith.URCGenerators.Family
import IndisputableMonolith.Verification.MetricFromUnitsCert
import IndisputableMonolith.Verification.MeasurementBridgeCert
import IndisputableMonolith.Verification.MatchesEvalCert
import IndisputableMonolith.Verification.PhiClosedDefaultsCert
import IndisputableMonolith.Verification.UniqueCalibrationCert
import IndisputableMonolith.Verification.TwoOutcomeBornCert
import IndisputableMonolith.Verification.KernelMatchCert
import IndisputableMonolith.Verification.PhiPinnedCert
import IndisputableMonolith.Verification.AlphaDerivationCert
import IndisputableMonolith.Verification.BornRuleDerivationCert

/-!
# Non-Circularity Certificate (Audit)

This module provides a **Lean-checkable audit certificate** that makes core “match”
claims explicit and non-vacuous.

## What this certificate does

It proves that:
- The *spec-level* dimensionless defaults are **explicit formulas in `φ`** (not arbitrary
  constants hidden behind opaque names).
- The *two-branch* Born-weight identity used by RS is proven via
  `IndisputableMonolith.Measurement.weight_equals_born` (i.e., not via `True` stubs).
- The “certified generators” slot is **non-vacuous** via `URCGenerators.VerifiedGenerators`.

## What this certificate does NOT do

It does **not** attempt to certify scaffold modules (e.g. the top-level `Quantum.lean`
`BoseFermiIface` placeholder, or the Relativity geometry scaffolds). Those are quarantined
separately and are intentionally excluded from the certificate chain.
-/

namespace IndisputableMonolith
namespace Verification
namespace NonCircularity

open IndisputableMonolith.RH

structure NonCircularityCert where
  deriving Repr

@[simp] def NonCircularityCert.verified (_c : NonCircularityCert) : Prop :=
  -- 1) The “dimensionless defaults” are explicit φ-formulas.
  (∀ φ : ℝ,
      RH.RS.alphaDefault φ = (1 - 1 / φ) / 2
      ∧ RH.RS.massRatiosDefault φ = [φ, 1 / (φ ^ (2 : Nat))]
      ∧ RH.RS.mixingAnglesDefault φ = [1 / φ]
      ∧ RH.RS.g2Default φ = 1 / (φ ^ (5 : Nat)))
  ∧
  -- 1a) The defaults are φ-closed: no hidden constants beyond `φ`.
  IndisputableMonolith.Verification.PhiClosedDefaults.PhiClosedDefaultsCert.verified {}
  ∧
  -- 1a) The computed match predicate routes through `MatchesEval` (not existential `Matches`),
  --     and the designated evaluator matches the explicit universal target.
  IndisputableMonolith.Verification.MatchesEval.MatchesEvalCert.verified {}
  ∧
  -- 1b) Absolute-layer calibration is explicit (unique RSUnits pack per anchors).
  IndisputableMonolith.Verification.UniqueCalibration.UniqueCalibrationCert.verified {}
  ∧
  -- 1c) φ pinning is explicit: there is a unique real satisfying the selection predicate.
  IndisputableMonolith.Verification.PhiPinned.PhiPinnedCert.verified {}
  ∧
  -- 1d) The kernel pointwise match used under the hood in `C = 2A` is proven.
  IndisputableMonolith.Verification.KernelMatch.KernelMatchCert.verified {}
  ∧
  -- 2) The Born-weight identity used in the RS spec actually holds (two-branch model).
  RH.RS.bornHolds
  ∧
  -- 2b) The underlying two-branch bridge identities (C = 2A, weight bridge) are proven.
  IndisputableMonolith.Verification.MeasurementBridge.MeasurementBridgeCert.verified {}
  ∧
  -- 2c) Normalized two-outcome probabilities match cos²/sin² (no MeasurementAxioms).
  IndisputableMonolith.Verification.TwoOutcomeBorn.TwoOutcomeBornCert.verified {}
  ∧
  -- 2d) Two-outcome Born rule derivation packaged at the probability level (axiom-free).
  IndisputableMonolith.Verification.BornRuleDerivation.BornRuleDerivationCert.verified {}
  ∧
  -- 3) The “RS measures reality” bundle has non-vacuous certified generators.
  (∀ φ : ℝ, URCGenerators.VerifiedGenerators φ)
  ∧
  -- 4) The K-display ratios are explicit and agree with the global K constant
  --     (under explicit nondegeneracy assumptions on anchors).
  (∀ U : IndisputableMonolith.Constants.RSUnits,
      U.tau0 ≠ 0 →
      U.ell0 ≠ 0 →
        (IndisputableMonolith.Constants.RSUnits.tau_rec_display U) / U.tau0 = IndisputableMonolith.Constants.K
        ∧ (IndisputableMonolith.Constants.RSUnits.lambda_kin_display U) / U.ell0 = IndisputableMonolith.Constants.K)
  ∧
  -- 5) Metric-from-units milestone: the Minkowski metric induced by RS units has
  --    a null anchor vector (light-cone condition).
  IndisputableMonolith.Verification.MetricFromUnits.MetricFromUnitsCert.verified {}
  ∧
  -- 6) Alpha formula provenance (no hard-coded numeric “match” theorems).
  IndisputableMonolith.Verification.AlphaDerivation.AlphaDerivationCert.verified {}

@[simp] theorem NonCircularityCert.verified_any (c : NonCircularityCert) :
    NonCircularityCert.verified c := by
  refine
    And.intro ?formulas
      (And.intro ?phiClosedDefaults
        (And.intro ?matchesEval
          (And.intro ?calibration
            (And.intro ?phiPinned
              (And.intro ?kernel
                (And.intro ?born
                  (And.intro ?bridge
                    (And.intro ?twoOutcome
                      (And.intro ?bornDeriv
                      (And.intro ?gens
                        (And.intro ?k
                          (And.intro ?metric ?alpha))))))))))))
  · intro φ
    refine And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))
    · rfl
    · rfl
    · rfl
    · rfl
  · exact IndisputableMonolith.Verification.PhiClosedDefaults.PhiClosedDefaultsCert.verified_any {}
  · exact IndisputableMonolith.Verification.MatchesEval.MatchesEvalCert.verified_any {}
  · exact IndisputableMonolith.Verification.UniqueCalibration.UniqueCalibrationCert.verified_any {}
  · exact IndisputableMonolith.Verification.PhiPinned.PhiPinnedCert.verified_any {}
  · exact IndisputableMonolith.Verification.KernelMatch.KernelMatchCert.verified_any {}
  · -- bornHolds is proven from the two-branch Measurement bridge theorem.
    exact RH.RS.born_from_TruthCore
  · exact IndisputableMonolith.Verification.MeasurementBridge.MeasurementBridgeCert.verified_any {}
  · exact IndisputableMonolith.Verification.TwoOutcomeBorn.TwoOutcomeBornCert.verified_any {}
  · exact IndisputableMonolith.Verification.BornRuleDerivation.BornRuleDerivationCert.verified_any {}
  · intro φ
    exact URCGenerators.demo_generators φ
  · intro U hτ hℓ
    exact IndisputableMonolith.Constants.RSUnits.K_gate_eqK U hτ hℓ
  · exact IndisputableMonolith.Verification.MetricFromUnits.MetricFromUnitsCert.verified_any {}
  · exact IndisputableMonolith.Verification.AlphaDerivation.AlphaDerivationCert.verified_any {}

end NonCircularity
end Verification
end IndisputableMonolith
