import IndisputableMonolith.RRF.Models.Quadratic
import IndisputableMonolith.RRF.Models.Trivial

/-!
# RRF Models

Umbrella file for RRF consistency models.

These are concrete examples that satisfy RRF axioms, proving internal consistency.

## Contents

- `Trivial`: The simplest model (Unit, J=0)
- `Quadratic`: A continuous model (ℝ, J=x²)
-/


namespace IndisputableMonolith
namespace RRF

/-- At least one model exists (consistency at universe 0). -/
theorem models_exist : Nonempty (Core.Octave.{0, 0, 0}) := Models.trivialModel_consistent

end RRF
end IndisputableMonolith
