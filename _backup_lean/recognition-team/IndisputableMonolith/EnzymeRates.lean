import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith/Compat

open Real Complex
open scoped BigOperators Matrix

/-!
Enzyme catalytic rate ceiling proxy locked to φ-rungs.

We model a dimensionless ceiling `rate_ceiling r = (1/φ)^r`, which is
strictly positive for all r. This provides a compiling statement for
certificates and reports without additional dependencies.
-/

namespace IndisputableMonolith
namespace Biology
namespace EnzymeRates

noncomputable def rate_ceiling (r : Nat) : ℝ := (1 / Constants.phi) ^ r

/-- Positivity of the rate ceiling for all r. -/
theorem ceiling_holds (r : Nat) : rate_ceiling r > 0 := by
  dsimp [rate_ceiling]
  have hφpos : 0 < Constants.phi := by
    have : 1 < Constants.phi := Constants.one_lt_phi
    exact lt_trans (by norm_num) this
  have ha_pos : 0 < (1 / Constants.phi) := inv_pos.mpr hφpos
  exact pow_pos ha_pos _

end EnzymeRates
end Biology
end IndisputableMonolith
