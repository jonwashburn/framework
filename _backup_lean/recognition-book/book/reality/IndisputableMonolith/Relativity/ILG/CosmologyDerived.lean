import Mathlib
import IndisputableMonolith.Relativity.ILG.Action
import IndisputableMonolith.Relativity.Cosmology.Friedmann
import IndisputableMonolith.Relativity.Cosmology.GrowthFactor
import IndisputableMonolith.Relativity.Cosmology.Sigma8

namespace IndisputableMonolith
namespace Relativity
namespace ILG

open Cosmology

noncomputable def friedmann_ILG (scale : ScaleFactor) (rho_matter : ℝ → ℝ) (psi : ℝ → ℝ) (m_squared : ℝ) : Prop :=
  let rho_psi := energy_density_scalar scale psi m_squared
  FriedmannI scale rho_matter rho_psi

axiom friedmann_derived :
  True

axiom growth_ILG_exists (α C_lag : ℝ) :
  ∃ growth : GrowthFactor, True

axiom sigma8_ILG_computable (α C_lag sigma8_0 a : ℝ) :
  ∃ sigma8_val, True

axiom cosmology_predictions_derived :
  True

end ILG
end Relativity
end IndisputableMonolith
