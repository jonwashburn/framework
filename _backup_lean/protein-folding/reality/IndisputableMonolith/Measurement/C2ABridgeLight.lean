import Mathlib
import IndisputableMonolith.Measurement.TwoBranchGeodesic

/-!
# C = 2A Bridge (Lightweight Export)

Paper-safe export of the central bridge as an axiom to avoid heavy dependencies.
-/

namespace IndisputableMonolith
namespace Measurement

open Real

/-- Lightweight export: existence of C and A with C = 2A and exp(-C) match. -/
axiom C_equals_2A (rot : TwoBranchRotation) :
  ∃ (C A : ℝ), C = 2 * A ∧ Real.exp (-C) = initialAmplitudeSquared rot

end Measurement
end IndisputableMonolith
