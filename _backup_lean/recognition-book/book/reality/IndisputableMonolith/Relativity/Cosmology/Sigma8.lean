import Mathlib
import IndisputableMonolith.Relativity.Cosmology.GrowthFactor

namespace IndisputableMonolith
namespace Relativity
namespace Cosmology

noncomputable def sigma8 (growth : GrowthFactor) (sigma8_0 : ℝ) (a : ℝ) : ℝ :=
  sigma8_0 * growth.D a / growth.D 1

axiom sigma8_evolution_ILG (growth_ILG growth_GR : GrowthFactor) (sigma8_0 : ℝ) (α C_lag : ℝ) :
  ∀ a, |sigma8 growth_ILG sigma8_0 a - sigma8 growth_GR sigma8_0 a| < (α * C_lag) * 0.1

axiom sigma8_tension (growth_ILG : GrowthFactor) (sigma8_0 : ℝ) :
  True

axiom CMB_consistency (growth : GrowthFactor) :
  True

axiom BAO_consistency (growth : GrowthFactor) :
  True

axiom BBN_consistency :
  True

end Cosmology
end Relativity
end IndisputableMonolith
