import Mathlib
import IndisputableMonolith.Causality.Reach
import IndisputableMonolith.LightCone
import IndisputableMonolith.Constants

/-!
Cone Bound Export Theorem

This module contains the verification-level cone bound theorem that exports
the discrete light-cone bound without the step count parameter.
-/

namespace IndisputableMonolith
namespace ConeExport

open Constants

section

variable {α : Type _}
variable (K : Causality.Kinematics α)
variable (U : Constants.RSUnits)
variable (time rad : α → ℝ)

/-- Verification-level cone bound: if per-step bounds hold, any `n`-step reach obeys
    `rad y - rad x ≤ U.c * (time y - time x)` with no `n` in the statement. -/
theorem cone_bound_export
  (H : LightCone.StepBounds K U time rad)
  {n x y} (h : Causality.ReachN K n x y) :
  rad y - rad x ≤ U.c * (time y - time x) := by
  simpa using (LightCone.StepBounds.cone_bound (K:=K) (U:=U) (time:=time) (rad:=rad) H h)

end

end ConeExport
end IndisputableMonolith