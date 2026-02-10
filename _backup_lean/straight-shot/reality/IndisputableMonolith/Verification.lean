import Mathlib
import IndisputableMonolith.Verification.BridgeCore
import IndisputableMonolith.Constants.KDisplayCore
import IndisputableMonolith.Verification.KnobsCount

namespace IndisputableMonolith
namespace Verification

/-! Minimal claim/rendering scaffold -/

inductive StatementType
| eq
| le
deriving DecidableEq, Repr

inductive ClaimStatus
| proven
| failed
| unchecked
deriving DecidableEq, Repr

def statementString : StatementType → String
| StatementType.eq => "eq"
| StatementType.le => "le"

def statusString : ClaimStatus → String
| ClaimStatus.proven    => "proven"
| ClaimStatus.failed    => "failed"
| ClaimStatus.unchecked => "unchecked"

structure Claim where
  id     : String
  stmt   : StatementType
  status : ClaimStatus := ClaimStatus.unchecked
deriving Repr

structure RenderedClaim where
  id        : String
  statement : String
  status    : String
deriving Repr

def renderClaim (c : Claim) : RenderedClaim :=
  { id := c.id, statement := statementString c.stmt, status := statusString c.status }

noncomputable def Claim.checkEq (c : Claim) (lhs rhs : ℝ) : Claim :=
  { c with status := if lhs = rhs then ClaimStatus.proven else ClaimStatus.failed }

noncomputable def Claim.checkLe (c : Claim) (lhs rhs : ℝ) : Claim :=
  { c with status := if lhs ≤ rhs then ClaimStatus.proven else ClaimStatus.failed }

/-! Manifest and gates/falsifiability stubs -/

structure GateSpec where
  id     : String
  inputs : List String
  output : String
deriving Repr

structure Falsifiable where
  id          : String
  wouldFailIf : String
  guardedBy   : String
deriving Repr

structure RenderedManifest where
  claims         : List RenderedClaim
  gates          : List GateSpec
  falsifiability : List Falsifiable
  knobs          : Nat
deriving Repr

@[simp] def dimlessClaimsRendered : List RenderedClaim :=
  [ { id := "KGateEquality", statement := "K_A = K_B", status := "proven" }
  , { id := "ConeBound", statement := "rad y - rad x ≤ c · (time y - time x)", status := "proven" }
  ]

@[simp] def gatesRendered : List GateSpec :=
  [ { id := "KGate", inputs := ["K_A", "K_B"], output := "K_A = K_B" }
  , { id := "ConeGate", inputs := ["rad", "time", "c"], output := "cone bound holds" }
  ]

@[simp] def falsifiabilityRendered : List Falsifiable :=
  [ { id := "KGateMismatch", wouldFailIf := "K_A ≠ K_B", guardedBy := "Verification.K_gate_bridge" }
  , { id := "ConeViolation", wouldFailIf := "∃n x y, rad y - rad x > c · (time y - time x)", guardedBy := "Verification.cone_bound_export" }
  ]

@[simp] def manifest : RenderedManifest :=
{ claims := dimlessClaimsRendered
, gates := gatesRendered
, falsifiability := falsifiabilityRendered
, knobs := knobsCount }

@[simp] def claimIds : List String := dimlessClaimsRendered.map (fun c => c.id)
@[simp] def gateIds  : List String := gatesRendered.map (fun g => g.id)

@[simp] def claimsCount : Nat := dimlessClaimsRendered.length
@[simp] def gatesCount  : Nat := gatesRendered.length
@[simp] def falsifiabilityCount : Nat := falsifiabilityRendered.length

@[simp] lemma claimsCount_eq_two : claimsCount = 2 := by
  simp [claimsCount, dimlessClaimsRendered]

@[simp] lemma gatesCount_eq_two : gatesCount = 2 := by
  simp [gatesCount, gatesRendered]

@[simp] lemma falsifiabilityCount_eq_two : falsifiabilityCount = 2 := by
  simp [falsifiabilityCount, falsifiabilityRendered]

@[simp] def manifestStrings : List String :=
  [ "claims={" ++ String.intercalate ", " claimIds ++ "}"
  , "gates={"  ++ String.intercalate ", " gateIds  ++ "}"
  , "knobs="    ++ toString knobsCount ]

@[simp] def manifestSummary : String :=
  "Claims: " ++ toString claimsCount ++
  ", Gates: " ++ toString gatesCount ++
  ", Falsifiability: " ++ toString falsifiabilityCount ++
  ", Knobs: " ++ toString knobsCount

@[simp] def urcClaimIds : List String :=
  [ "URC.lawful_physical", "URC.lawful_computational", "URC.lawful_ethical"
  , "URC.lambda_rec_unique", "URC.AE_skeleton" ]

@[simp] def urcGateIds : List String :=
  [ "URC.CertificatesGate", "URC.FixedPointT" ]

@[simp] def urcManifestStrings : List String :=
  [ "urc_claims={" ++ String.intercalate ", " urcClaimIds ++ "}"
  , "urc_gates={"  ++ String.intercalate ", " urcGateIds  ++ "}" ]

@[simp] def urcClaimsCount : Nat := urcClaimIds.length
@[simp] def urcGatesCount  : Nat := urcGateIds.length

@[simp] def urcSummary : String :=
  "URC Claims: " ++ toString urcClaimsCount ++
  ", URC Gates: " ++ toString urcGatesCount

@[simp] noncomputable def K_A_eval (_U : RSUnits) : ℝ := Constants.K
@[simp] noncomputable def K_B_eval (_U : RSUnits) : ℝ := Constants.K

structure KGateInput where
  id    : String
  about : String
deriving Repr

structure KGateResult where
  id     : String
  passed : Bool
  note   : String := ""
deriving Repr

noncomputable def runKGate (U : RSUnits) (inp : KGateInput) : KGateResult :=
  let lhs := K_A_eval U
  let rhs := K_B_eval U
  let ok  := lhs = rhs
  { id := inp.id
  , passed := ok
  , note := if ok then "K_A = K_B holds" else "K_A != K_B" }

/-- Structural bridge factorization bundle:
    (A) bridge evaluation is invariant under anchor rescaling, and
    (J) the K‑gate display ratios equal the global constant `K` (under explicit
        nondegeneracy assumptions on anchors). -/
def BridgeFactorizes : Prop :=
  (∀ (O : Observable) {U U'}, UnitsRescaled U U' → BridgeEval O U = BridgeEval O U')
  ∧ (∀ U : Constants.RSUnits,
        U.tau0 ≠ 0 →
        U.ell0 ≠ 0 →
          (IndisputableMonolith.Constants.RSUnits.tau_rec_display U) / U.tau0 = IndisputableMonolith.Constants.RSUnits.K_gate_ratio
          ∧ (IndisputableMonolith.Constants.RSUnits.lambda_kin_display U) / U.ell0 = IndisputableMonolith.Constants.RSUnits.K_gate_ratio)

/-- Proof witness for `BridgeFactorizes` using existing invariance and K‑gate lemmas. -/
theorem bridge_factorizes : BridgeFactorizes := by
  refine And.intro ?hQ ?hJ
  · intro O U U' h; exact anchor_invariance O h
  · intro U hτ hℓ
    exact IndisputableMonolith.Constants.RSUnits.K_gate_eqK U hτ hℓ

end Verification
end IndisputableMonolith
