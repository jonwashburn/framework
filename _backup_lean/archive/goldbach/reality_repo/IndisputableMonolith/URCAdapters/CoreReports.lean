import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Bridge.Data
import IndisputableMonolith.Verification
import IndisputableMonolith.Chain
import IndisputableMonolith.Potential
import IndisputableMonolith.LightCone.StepBounds
import IndisputableMonolith.Patterns
import IndisputableMonolith.PhiSupport.Lemmas

namespace IndisputableMonolith
namespace URCAdapters

/-- Minimal audit: force elaboration of core theorems only.
    This avoids importing broader WIP domains. -/
@[simp] def audit_dashboard_core_report : String :=
  -- K-gate route identity (BridgeEval K_A = BridgeEval K_B)
  let U : IndisputableMonolith.Constants.RSUnits :=
    { tau0 := 1, ell0 := 1, c := 1, c_ell0_tau0 := by simp }
  let _ := IndisputableMonolith.Verification.K_gate_bridge U

  -- λ_rec identity (physical witness)
  let B : IndisputableMonolith.BridgeData :=
    { G := 1, hbar := 1, c := 1, tau0 := 1, ell0 := 1 }
  let H : IndisputableMonolith.BridgeData.Physical B :=
    { c_pos := by norm_num, hbar_pos := by norm_num, G_pos := by norm_num }
  let _ := IndisputableMonolith.BridgeData.lambda_rec_dimensionless_id_physical B H

  -- Exactness (T3/T4) – reference the core theorems directly
  let _ := @IndisputableMonolith.T3_continuity
  let _ := @IndisputableMonolith.Potential.T4_unique_on_component

  -- Eight‑tick minimality witness
  let _ := IndisputableMonolith.Patterns.period_exactly_8

  -- Cone bound (step-level light-cone inequality)
  let _ := @IndisputableMonolith.LightCone.StepBounds.cone_bound

  -- φ uniqueness (unique positive solution of x² = x + 1)
  let _ := IndisputableMonolith.PhiSupport.phi_unique_pos_root

  "AUDIT CORE: OK (KGate, LambdaRec, Exactness, EightTick, ConeBound, PhiUnique)"

/-- Thin master report (core-only): elaborates the master bundle with light deps. -/
@[simp] def reality_master_core_report : String :=
  let φ : ℝ := IndisputableMonolith.Constants.phi
  let _ := IndisputableMonolith.Verification.Reality.rs_reality_master_any φ
  "RSRealityMaster(Core): OK"

end URCAdapters
end IndisputableMonolith


