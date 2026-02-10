import Mathlib
import IndisputableMonolith.Constants

/-!
Morphogen gradient precision proxy tied to a φ-based noise floor.

We define a positive φ-noise `phi_noise = 1/φ` and a unit scale, and
show that the precision `1/(noise*scale)` is strictly positive.
This minimal statement compiles and can be used in certificates/reports.
-/

namespace IndisputableMonolith
namespace Biology
namespace Morphogen

noncomputable def phi_noise : ℝ := 1 / IndisputableMonolith.Constants.phi

@[simp] noncomputable def gradient_scale : ℝ := 1

noncomputable def morphogen_precision (noise scale : ℝ) : ℝ := 1 / (noise * scale)

/-- Precision is strictly positive for φ-noise and unit scale. -/
theorem precision_holds : morphogen_precision phi_noise gradient_scale > 0 := by
  dsimp [morphogen_precision, phi_noise, gradient_scale]
  have hφpos : 0 < IndisputableMonolith.Constants.phi := by
    have : 1 < IndisputableMonolith.Constants.phi := IndisputableMonolith.Constants.one_lt_phi
    exact lt_trans (by norm_num) this
  have hnoise : 0 < 1 / IndisputableMonolith.Constants.phi := inv_pos.mpr hφpos
  have hscale : 0 < (1 : ℝ) := by norm_num
  have hprod : 0 < (1 / IndisputableMonolith.Constants.phi) * (1 : ℝ) := mul_pos hnoise hscale
  exact inv_pos.mpr (by
    -- noise*scale > 0 ⇒ 1/(noise*scale) > 0
    simpa using hprod)

end Morphogen
end Biology
end IndisputableMonolith
