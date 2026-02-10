import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.PhiSupport

namespace IndisputableMonolith
namespace Cost

/-- Canonical lemma: φ is the positive solution of x = 1 + 1/x. -/
lemma phi_is_cost_fixed_point : Constants.phi = 1 + 1 / Constants.phi := by
  simpa using IndisputableMonolith.PhiSupport.phi_fixed_point

end Cost
end IndisputableMonolith