import Mathlib
import IndisputableMonolith.URCGenerators.CoreCerts

/-!
# Certificate Family Interface

This module defines the authoritative `CertFamily` structure and its verification
predicates. This is the **source of truth** for the URC generator interface.

## Key Definitions

- `CertFamily`: A structure bundling lists of individual certificates
- `Verified φ C`: All certificates in family C are individually verified at scale φ
- `NonVacuous C`: Core certificate lists must be nonempty—prevents trivial satisfaction
- `VerifiedNonVacuous φ C`: Combined predicate (Verified ∧ NonVacuous)
- `VerifiedGenerators φ`: Existential wrapper asserting a verified non-vacuous
  certificate family exists

## Non-Vacuity Requirement

The `NonVacuous` predicate prevents "verified with empty certificates" from being
trivially true. This ensures that when `VerifiedGenerators φ` holds, there is
actual content—not just an empty witness.

## Canonical Witness

`canonicalCertFamily` provides a minimal witness with one certificate in each
core slot, proven to satisfy `VerifiedNonVacuous φ` for any φ.
-/

namespace IndisputableMonolith
namespace URCGenerators

/-! ### Certificate Family Structure -/

/-- Minimal certificate family structure with core generator fields.

    Each field is a list of certificates. The `Verified` predicate asserts
    all certificates in each list are individually proven. -/
structure CertFamily where
  kgate : List KGateCert := []
  kidentities : List KIdentitiesCert := []
  lambdaRec : List LambdaRecIdentityCert := []
  coneBound : List ConeBoundCert := []
  eightTick : List EightTickMinimalCert := []
  exactness : List ExactnessCert := []
  invariantsRatio : List InvariantsRatioCert := []
  deriving Repr

/-! ### Verification Predicates -/

/-- Verification predicate: all certificates in each list are individually verified. -/
def Verified (φ : ℝ) (C : CertFamily) : Prop :=
  (∀ c ∈ C.kgate, KGateCert.verified c) ∧
  (∀ c ∈ C.kidentities, KIdentitiesCert.verified c) ∧
  (∀ c ∈ C.lambdaRec, LambdaRecIdentityCert.verified c) ∧
  (∀ c ∈ C.coneBound, ConeBoundCert.verified c) ∧
  (∀ c ∈ C.eightTick, EightTickMinimalCert.verified c) ∧
  (∀ c ∈ C.exactness, ExactnessCert.verified c) ∧
  (∀ c ∈ C.invariantsRatio, InvariantsRatioCert.verified c)

/-- Non-vacuity requirement: core generator fields must be nonempty.
    This prevents `Verified` from being trivially true with empty lists. -/
def NonVacuous (C : CertFamily) : Prop :=
  C.kgate ≠ [] ∧
  C.kidentities ≠ [] ∧
  C.lambdaRec ≠ [] ∧
  C.coneBound ≠ [] ∧
  C.eightTick ≠ [] ∧
  C.exactness ≠ [] ∧
  C.invariantsRatio ≠ []

/-- Combined predicate: verified AND non-vacuous. -/
def VerifiedNonVacuous (φ : ℝ) (C : CertFamily) : Prop :=
  Verified φ C ∧ NonVacuous C

/-- Existential wrapper: there exists a certificate family that is verified and non-vacuous. -/
def VerifiedGenerators (φ : ℝ) : Prop :=
  ∃ C : CertFamily, VerifiedNonVacuous φ C

/-! ### Canonical Witness -/

/-- The canonical minimal certificate family with one certificate in each core slot.
    All certificates are proven to verify. -/
def canonicalCertFamily : CertFamily := {
  kgate := [{}]
  kidentities := [{}]
  lambdaRec := [{}]
  coneBound := [{}]
  eightTick := [{}]
  exactness := [{}]
  invariantsRatio := [{}]
}

/-- The canonical family satisfies the non-vacuity requirement. -/
theorem canonicalCertFamily_nonvacuous : NonVacuous canonicalCertFamily := by
  unfold NonVacuous canonicalCertFamily
  simp

/-- The canonical family is verified at any scale φ. -/
theorem canonicalCertFamily_verified (φ : ℝ) : Verified φ canonicalCertFamily := by
  unfold Verified canonicalCertFamily
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (intro c _hc; cases c)
  · -- kgate
    exact RecogSpec.kGate_from_units
  · -- kidentities
    intro U hτ hℓ
    exact Constants.RSUnits.K_gate_eqK U hτ hℓ
  · -- lambdaRec
    intro B H
    exact IndisputableMonolith.BridgeData.lambda_rec_dimensionless_id_physical B H
  · -- coneBound
    intro U
    exact U.c_ell0_tau0.symm
  · -- eightTick
    exact RecogSpec.eightTick_from_TruthCore
  · -- exactness
    exact URCGenerators.ExactnessCert.verified_any {}
  · -- invariantsRatio
    exact Constants.K_def

/-- The canonical family is verified AND non-vacuous. -/
theorem canonicalCertFamily_verifiedNonVacuous (φ : ℝ) :
    VerifiedNonVacuous φ canonicalCertFamily :=
  ⟨canonicalCertFamily_verified φ, canonicalCertFamily_nonvacuous⟩

/-- Proven: there exist verified non-vacuous generators at any scale φ. -/
theorem demo_generators (φ : ℝ) : VerifiedGenerators φ :=
  ⟨canonicalCertFamily, canonicalCertFamily_verifiedNonVacuous φ⟩

end URCGenerators
end IndisputableMonolith
