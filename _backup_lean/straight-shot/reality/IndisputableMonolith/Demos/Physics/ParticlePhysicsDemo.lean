import IndisputableMonolith.Physics.ParticleSummary
import IndisputableMonolith.Verification.AdvancedParticlePhysicsCert

/-!
# Particle Physics Demo: Standard Model Derivation
This demo showcases the Standard Model parameters derived from the
Recognition Science geometric foundations.
-/

open IndisputableMonolith.Physics.Summary
open IndisputableMonolith.Verification.AdvancedParticlePhysics

def main : IO Unit := do
  let params := derived_parameters

  IO.println "--- Recognition Science: Particle Physics Derivations ---"
  IO.println s!"Cabibbo Angle (V_us): {params.cabibbo_angle_Vus}"
  IO.println s!"CKM V_cb:            {params.ckm_Vcb}"
  IO.println s!"CKM V_ub:            {params.ckm_Vub}"
  IO.println s!"PMNS sin²θ₁₃:        {params.pmns_sin2_theta13}"
  IO.println s!"PMNS sin²θ₁₂:        {params.pmns_sin2_theta12}"
  IO.println s!"PMNS sin²θ₂₃:        {params.pmns_sin2_theta23}"
  IO.println ""
  IO.println s!"Alpha⁻¹ (Locked):    {params.alpha_inv_lock}"
  IO.println s!"QCD Beta₀:           {params.qcd_b0}"
  IO.println ""
  IO.println s!"Lepton Rungs:        {params.lepton_rungs}"
  IO.println s!"Quark Steps:         {params.quark_steps}"
  IO.println "------------------------------------------------"

  IO.println "Status: Particle Physics Verification Certificate found."

#check particle_physics_verified
