import Mathlib
import IndisputableMonolith.Constants

open Real Complex
open scoped BigOperators Matrix

/-!
Bond-angle chirality bias proxy from φ-lattice.

We avoid heavy trigonometry and encode a dimensionless bias proxy
`tetra_bias := 1 - 1/φ`, which is strictly positive since φ>1.
This captures the intended preference (away from zero) in a minimal,
compiling form usable by certificates and reports.
-/

namespace IndisputableMonolith
namespace Chemistry

/-- Dimensionless bias proxy for tetrahedral preference. -/
noncomputable def tetra_bias : ℝ := 1 - (1 / Constants.phi)

/-- The bias proxy is strictly positive (since φ>1 ⇒ 1/φ<1). -/
theorem angle_bias : 0 < tetra_bias := by
  dsimp [tetra_bias]
  have hφ : 1 < Constants.phi := Constants.one_lt_phi
  have hφpos : 0 < Constants.phi := lt_trans (by norm_num) hφ
  have : (1 / Constants.phi) < 1 := by
    -- `a / b < 1 ↔ a < b` for `b > 0`.
    have hiff : (1 : ℝ) / Constants.phi < 1 ↔ (1 : ℝ) < Constants.phi :=
      div_lt_one hφpos
    exact hiff.mpr hφ
  have : 0 < 1 - (1 / Constants.phi) := sub_pos.mpr this
  simpa using this

end Chemistry
end IndisputableMonolith
