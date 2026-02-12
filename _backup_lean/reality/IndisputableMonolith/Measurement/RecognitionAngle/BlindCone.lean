import Mathlib
import IndisputableMonolith.Measurement.RecognitionAngle.ActionSmallAngle

/-!
# Recognition Blind Cone: Definitions and Basic Properties

Defines the blind-cone set at a point `x` for a given action budget `Amax` and
proves existence of a positive threshold angle under `Amax>0`.
-/

noncomputable section

open scoped Real

namespace IndisputableMonolith
namespace Measurement
namespace RecognitionAngle

abbrev R3 := EuclideanSpace ℝ (Fin 3)

/-- Budget-dependent minimal angle threshold. -/
@[simp] def θmin (Amax : ℝ) : ℝ := thetaMin Amax

/-- The blind cone at `x` with budget `Amax`: pairs `(y,z)` whose separation angle at `x`
falls below `θmin(Amax)`. -/
def blindCone (x : R3) (Amax : ℝ) : Set (R3 × R3) :=
  { p | angleAt x p.1 p.2 < θmin Amax }

/-- Existence of a strictly positive threshold angle for any `Amax>0`. -/
theorem blind_cone_exists {Amax : ℝ} (hA : 0 < Amax) : 0 < θmin Amax := by
  have h := theta_min_range (Amax := Amax) hA
  exact h.left

/-- Upper bound: `θmin(Amax) ≤ π/2` for any `Amax>0`. Useful for cap-measure bounds. -/
theorem theta_min_le_pi_half {Amax : ℝ} (hA : 0 < Amax) : θmin Amax ≤ π/2 := by
  have h := theta_min_range (Amax := Amax) hA
  exact h.right

end RecognitionAngle
end Measurement
end IndisputableMonolith
