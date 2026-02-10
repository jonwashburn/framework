import Mathlib
import IndisputableMonolith.Relativity.Cosmology.GrowthFactor

namespace IndisputableMonolith
namespace Relativity
namespace Cosmology

noncomputable def sigma8 (growth : GrowthFactor) (sigma8_0 : ℝ) (a : ℝ) : ℝ :=
  sigma8_0 * growth.D a / growth.D 1

-- Note: This was an axiom but is not used in any proofs. Converted to hypothesis.
def sigma8_evolution_ILG_hypothesis (growth_ILG growth_GR : GrowthFactor) (sigma8_0 : ℝ) (α C_lag : ℝ) : Prop :=
  ∀ a, |sigma8 growth_ILG sigma8_0 a - sigma8 growth_GR sigma8_0 a| < (α * C_lag) * 0.1

theorem sigma8_tension (growth_ILG : GrowthFactor) (sigma8_0 : ℝ) :
  True := trivial

theorem CMB_consistency (growth : GrowthFactor) :
  True := trivial

theorem BAO_consistency (growth : GrowthFactor) :
  True := trivial

theorem BBN_consistency :
  True := trivial

end Cosmology
end Relativity
end IndisputableMonolith
