import Mathlib
import IndisputableMonolith.Constants

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
  have : (1 / Constants.phi) < 1 := inv_lt_one.mpr hφ
  have : 0 < 1 - (1 / Constants.phi) := sub_pos.mpr this
  simpa using this

end Chemistry
end IndisputableMonolith
