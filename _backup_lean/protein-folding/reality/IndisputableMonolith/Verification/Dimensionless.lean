import Mathlib
import IndisputableMonolith.Verification

namespace IndisputableMonolith
namespace Verification

/-- Any constant-valued display is dimensionless. -/
@[simp] lemma dimensionless_const (c : ℝ) : Dimensionless (fun (_ : Constants.RSUnits) => c) := by
  intro U U' h; rfl

end Verification
end IndisputableMonolith
