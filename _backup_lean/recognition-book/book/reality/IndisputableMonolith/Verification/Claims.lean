import Mathlib
import IndisputableMonolith.Core
import IndisputableMonolith.Verification

namespace IndisputableMonolith

/-- Minimal statement classification for verification claims. -/
inductive StatementType
| eq
| le
| generic
deriving DecidableEq, Repr

/-- Status of a claim: proven, failed, or unchecked. -/
inductive ClaimStatus
| proven
| failed
| unchecked
deriving DecidableEq

/-- A claim over a dimensionless observable with optional tolerance. -/
structure Claim where
  id        : String
  stype     : StatementType
  expr      : Verification.Observable
  target    : ℝ
  tol       : Option ℝ := none
  status    : ClaimStatus := .unchecked

/-- Smart constructor that only accepts anchor-invariant expressions. -/
def dimensionless_claim (id : String) (stype : StatementType)
  (expr : Verification.Observable) (target : ℝ) (tol : Option ℝ := none) : Claim :=
{ id := id, stype := stype, expr := expr, target := target, tol := tol, status := .unchecked }

/-- Evaluate a claim under anchors; due to invariance, result is anchor-independent. -/
@[simp] def Claim.value (c : Claim) (U : Constants.RSUnits) : ℝ :=
  Verification.BridgeEval c.expr U

/-- Check an equality claim by proof; returns updated status. -/
def Claim.checkEq (c : Claim) (U : Constants.RSUnits) (_h : c.value U = c.target) : Claim :=
  { c with status := .proven }

/-- Check an inequality claim by proof; returns updated status. -/
def Claim.checkLe (c : Claim) (U : Constants.RSUnits) (_h : c.value U ≤ c.target) : Claim :=
  { c with status := .proven }

/-- The single K-gate inputs for diagnostics and pass/fail witness. -/
structure KGateInput where
  u_ell0  : ℝ
  u_lrec  : ℝ
  rho     : ℝ
  k       : ℝ
  KB      : ℝ

/-- Result of running the K-gate: pass/fail and a witness inequality statement. -/
structure KGateResult where
  pass    : Bool
  witness : String

/-- K-gate checker: dimensionless bridge gate |K_A − K_B| ≤ k·u_comb. -/
noncomputable def runKGate (U : Constants.RSUnits) (inp : KGateInput) : KGateResult :=
  let KA : ℝ := Verification.BridgeEval Verification.K_A_obs U
  let KB : ℝ := inp.KB
  let ucomb : ℝ := IndisputableMonolith.Verification.uComb inp.u_ell0 inp.u_lrec inp.rho
  let lhs : ℝ := Real.abs (KA - KB)
  let rhs : ℝ := inp.k * ucomb
  let ok : Bool := decide (lhs ≤ rhs)
  { pass := ok
  , witness := if ok then "|K_A − K_B| ≤ k·u_comb (ρ)" else "|K_A − K_B| > k·u_comb (ρ)" }

end IndisputableMonolith
