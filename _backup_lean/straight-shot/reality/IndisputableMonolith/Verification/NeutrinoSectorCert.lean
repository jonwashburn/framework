import Mathlib
import IndisputableMonolith.Physics.NeutrinoSector
import IndisputableMonolith.Physics.MixingDerivation

/-!
# Neutrino Sector Certificate (hard‑falsifiable end‑to‑end)

This certificate bundles the **parameter‑free** neutrino mass‑scale predictions
(including Δm² bounds) together with the **PMNS mixing angle** and **Jarlskog**
matches proven in Lean.

Importantly, this certificate does **not** assume or assert existence of a global
PMNS unitary matrix realizing a specific weight tensor; it only packages the
numeric, experimentally checkable claims that are already proved.
-/

namespace IndisputableMonolith
namespace Verification
namespace NeutrinoSectorCert

open IndisputableMonolith.Physics

structure Cert where

  -- Absolute mass scale (fractional rungs; parameter‑free)
  nu3_bounds :
      (0.04987 : ℝ) < Physics.NeutrinoSector.predicted_mass_eV_frac Physics.NeutrinoSector.res_nu3 ∧
      Physics.NeutrinoSector.predicted_mass_eV_frac Physics.NeutrinoSector.res_nu3 < (0.04993 : ℝ)
  nu2_bounds :
      (0.00924 : ℝ) < Physics.NeutrinoSector.predicted_mass_eV_frac Physics.NeutrinoSector.res_nu2 ∧
      Physics.NeutrinoSector.predicted_mass_eV_frac Physics.NeutrinoSector.res_nu2 < (0.00928 : ℝ)
  nu1_bounds :
      (0.00352 : ℝ) < Physics.NeutrinoSector.predicted_mass_eV_frac Physics.NeutrinoSector.res_nu1 ∧
      Physics.NeutrinoSector.predicted_mass_eV_frac Physics.NeutrinoSector.res_nu1 < (0.00355 : ℝ)

  -- Mass‑squared splittings (compared to NuFIT intervals)
  dm2_21_in_nufit_1sigma :
      (7.21e-5 : ℝ) < Physics.NeutrinoSector.dm2_21_frac_pred ∧
      Physics.NeutrinoSector.dm2_21_frac_pred < (7.62e-5 : ℝ)
  dm2_31_in_nufit_2sigma :
      (2.455e-3 : ℝ) < Physics.NeutrinoSector.dm2_31_frac_pred ∧
      Physics.NeutrinoSector.dm2_31_frac_pred < (2.567e-3 : ℝ)

  -- Structural reason for φ⁷ in the squared‑mass ratio
  dm2_ratio_phi7 :
      (Real.goldenRatio ^ (IndisputableMonolith.Support.RungFractions.toReal Physics.NeutrinoSector.res_nu3)) ^ (2 : ℕ) /
          (Real.goldenRatio ^ (IndisputableMonolith.Support.RungFractions.toReal Physics.NeutrinoSector.res_nu2)) ^ (2 : ℕ)
        = Real.goldenRatio ^ (7 : ℝ)

  -- PMNS mixing (angle matches + Jarlskog)
  theta13_match : abs (Physics.MixingDerivation.sin2_theta13_pred - 0.022) < 0.002
  theta12_match : abs (Physics.MixingDerivation.sin2_theta12_pred - 0.307) < 0.01
  theta23_match : abs (Physics.MixingDerivation.sin2_theta23_pred - 0.546) < 0.01
  jarlskog_match : abs (Physics.MixingDerivation.jarlskog_pred - 3.08e-5) < 0.6e-5
  jarlskog_pos : Physics.MixingDerivation.jarlskog_pred > 0

def cert : Cert where
  nu3_bounds := Physics.NeutrinoSector.nu3_frac_pred_bounds
  nu2_bounds := Physics.NeutrinoSector.nu2_frac_pred_bounds
  nu1_bounds := Physics.NeutrinoSector.nu1_frac_pred_bounds
  dm2_21_in_nufit_1sigma := Physics.NeutrinoSector.dm2_21_frac_pred_in_nufit_1sigma
  dm2_31_in_nufit_2sigma := Physics.NeutrinoSector.dm2_31_frac_pred_in_nufit_2sigma
  dm2_ratio_phi7 := Physics.NeutrinoSector.squared_mass_ratio_structural_phi7
  theta13_match := Physics.MixingDerivation.pmns_theta13_match
  theta12_match := Physics.MixingDerivation.pmns_theta12_match
  theta23_match := Physics.MixingDerivation.pmns_theta23_match
  jarlskog_match := Physics.MixingDerivation.jarlskog_match
  jarlskog_pos := Physics.MixingDerivation.jarlskog_pos

end NeutrinoSectorCert
end Verification
end IndisputableMonolith
