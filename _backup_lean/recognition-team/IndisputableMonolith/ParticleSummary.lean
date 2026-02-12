import IndisputableMonolith.Physics.MixingDerivation
import IndisputableMonolith.Physics.RunningCouplings
import IndisputableMonolith.Physics.LeptonGenerations.Necessity
import IndisputableMonolith.Physics.QuarkMasses
import IndisputableMonolith.Physics.NeutrinoSector
import IndisputableMonolith.Physics.AnomalousMoments
import IndisputableMonolith.Physics.Hadrons
import IndisputableMonolith.Physics.MixingGeometry

namespace IndisputableMonolith.Physics.Summary

/-- Standard Model Parameters derived from Recognition Science. -/
structure SMDerivation where
  -- Mixing
  cabibbo_angle_Vus : ℝ
  ckm_Vcb : ℝ
  ckm_Vub : ℝ
  pmns_sin2_theta13 : ℝ
  pmns_sin2_theta12 : ℝ
  pmns_sin2_theta23 : ℝ
  -- Coupling
  alpha_inv_lock : ℝ
  qcd_b0 : ℝ
  -- Hierarchy
  lepton_rungs : List ℤ
  quark_steps : List ℚ

/-- Derived parameters from the geometric foundations. -/
noncomputable def derived_parameters : SMDerivation := {
  cabibbo_angle_Vus := MixingDerivation.V_us_pred
  ckm_Vcb := MixingDerivation.V_cb_pred
  ckm_Vub := MixingDerivation.V_ub_pred
  pmns_sin2_theta13 := MixingDerivation.sin2_theta13_pred
  pmns_sin2_theta12 := MixingDerivation.sin2_theta12_pred
  pmns_sin2_theta23 := MixingDerivation.sin2_theta23_pred
  alpha_inv_lock := 1 / Constants.alphaLock
  qcd_b0 := RunningCouplings.b0_qcd_rs
  lepton_rungs := [RSBridge.rung .e, RSBridge.rung .mu, RSBridge.rung .tau]
  quark_steps := [MixingGeometry.step_top_bottom, MixingGeometry.step_bottom_charm, MixingGeometry.step_charm_strange]
}

end IndisputableMonolith.Physics.Summary
