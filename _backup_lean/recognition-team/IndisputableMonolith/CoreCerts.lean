import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Constants.KDisplayCore
import IndisputableMonolith.Bridge.DataCore
import IndisputableMonolith.RecogSpec.Spec
import IndisputableMonolith.RecogSpec.PhiSelectionCore
import IndisputableMonolith.PhiSupport.Lemmas

/-!
# Core Certificate Types for CertFamily

This module defines the minimal set of certificate types used in `CertFamily`.
These are the authoritative definitions for the URC generator interface.

## Certificate Types

- `KGateCert`: K-gate identity holds for all unit systems
- `KIdentitiesCert`: τ_rec/τ₀ = K and λ_kin/ℓ₀ = K
- `LambdaRecIdentityCert`: λ_rec dimensionless identity
- `ConeBoundCert`: ℓ₀ = c · τ₀ light-cone constraint
- `EightTickMinimalCert`: Minimal 8-tick witness (Patterns complete cover of period 8)
- `ExactnessCert`: φ is uniquely pinned by the selection predicate
- `InvariantsRatioCert`: K = φ^(1/2) identity

Each certificate type has:
1. A structure (often empty, acting as a witness token)
2. A `verified` predicate defining what the certificate asserts
3. A `verified_any` theorem proving the predicate holds
-/

namespace IndisputableMonolith
namespace URCGenerators

/-! ### K-Gate Certificate -/

structure KGateCert where deriving Repr

@[simp] def KGateCert.verified (_c : KGateCert) : Prop :=
  RecogSpec.kGateWitness

@[simp] theorem KGateCert.verified_any (c : KGateCert) : KGateCert.verified c :=
  RecogSpec.kGate_from_units

/-! ### K-Identities Certificate -/

structure KIdentitiesCert where deriving Repr

@[simp] def KIdentitiesCert.verified (_c : KIdentitiesCert) : Prop :=
  ∀ U : Constants.RSUnits,
    U.tau0 ≠ 0 →
    U.ell0 ≠ 0 →
      (Constants.RSUnits.tau_rec_display U) / U.tau0 = Constants.K ∧
      (Constants.RSUnits.lambda_kin_display U) / U.ell0 = Constants.K

@[simp] theorem KIdentitiesCert.verified_any (c : KIdentitiesCert) : KIdentitiesCert.verified c :=
  fun U hτ hℓ => Constants.RSUnits.K_gate_eqK U hτ hℓ

/-! ### Lambda-Rec Identity Certificate -/

structure LambdaRecIdentityCert where deriving Repr

@[simp] def LambdaRecIdentityCert.verified (_c : LambdaRecIdentityCert) : Prop :=
  ∀ (B : IndisputableMonolith.BridgeData.BridgeData),
    IndisputableMonolith.BridgeData.Physical B →
      (B.c ^ 3) * (IndisputableMonolith.BridgeData.lambda_rec B) ^ 2 / (B.hbar * B.G)
        = 1 / Real.pi

@[simp] theorem LambdaRecIdentityCert.verified_any (c : LambdaRecIdentityCert) :
    LambdaRecIdentityCert.verified c :=
  fun B H => IndisputableMonolith.BridgeData.lambda_rec_dimensionless_id_physical B H

/-! ### Cone Bound Certificate -/

structure ConeBoundCert where deriving Repr

@[simp] def ConeBoundCert.verified (_c : ConeBoundCert) : Prop :=
  ∀ U : Constants.RSUnits, U.ell0 = U.c * U.tau0

@[simp] theorem ConeBoundCert.verified_any (c : ConeBoundCert) : ConeBoundCert.verified c :=
  fun U => U.c_ell0_tau0.symm

/-! ### Eight-Tick Minimal Certificate -/

structure EightTickMinimalCert where deriving Repr

@[simp] def EightTickMinimalCert.verified (_c : EightTickMinimalCert) : Prop :=
  RecogSpec.eightTickWitness

@[simp] theorem EightTickMinimalCert.verified_any (c : EightTickMinimalCert) :
    EightTickMinimalCert.verified c :=
  RecogSpec.eightTick_from_TruthCore

/-! ### Exactness Certificate -/

structure ExactnessCert where deriving Repr

@[simp] def ExactnessCert.verified (_c : ExactnessCert) : Prop :=
  ∃! φ : ℝ, RecogSpec.PhiSelection φ

@[simp] theorem ExactnessCert.verified_any (c : ExactnessCert) : ExactnessCert.verified c :=
  by
    refine ⟨IndisputableMonolith.Constants.phi, ?_, ?_⟩
    · -- PhiSelection for Constants.phi
      constructor
      · simpa using IndisputableMonolith.PhiSupport.phi_squared
      · exact lt_trans (by norm_num : (0 : ℝ) < 1) IndisputableMonolith.PhiSupport.one_lt_phi
    · intro x hx
      exact (IndisputableMonolith.PhiSupport.phi_unique_pos_root x).mp hx

/-! ### Invariants Ratio Certificate -/

structure InvariantsRatioCert where deriving Repr

@[simp] def InvariantsRatioCert.verified (_c : InvariantsRatioCert) : Prop :=
  Constants.K = (Constants.phi ^ (1/2 : ℝ))

@[simp] theorem InvariantsRatioCert.verified_any (c : InvariantsRatioCert) :
    InvariantsRatioCert.verified c :=
  Constants.K_def

end URCGenerators
end IndisputableMonolith
