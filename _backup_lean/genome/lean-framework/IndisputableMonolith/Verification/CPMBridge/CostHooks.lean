import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Cost.Convexity
import IndisputableMonolith.Cost.FunctionalEquation
import IndisputableMonolith.CPM.LawOfExistence
import IndisputableMonolith.CostUniqueness

namespace IndisputableMonolith
namespace Verification
namespace CPMBridge

open Cost

/-- Witness that Jcost satisfies the T4/T5 uniqueness hypothesis bundle. -/
def Jcost_satisfies_axioms : CostUniqueness.UniqueCostAxioms Jcost :=
  { symmetric := fun hx => Jcost_symm hx
  , unit := Jcost_unit0
  , convex := IndisputableMonolith.Cost.Convexity.Jcost_strictConvexOn_pos
  , calibrated := by
      -- d^2/dt^2 (J ∘ exp) at t=0 equals 1 (normalization)
      simpa using IndisputableMonolith.CPM.LawOfExistence.RS.Jcost_log_second_deriv_normalized
  , continuousOn_pos := IndisputableMonolith.CostUniqueness.Jcost_continuous_pos
  , coshAdd := IndisputableMonolith.Cost.FunctionalEquation.Jcost_cosh_add_identity }

/-- T5 consequence: any admissible cost equals J on (0,∞). -/
theorem any_admissible_cost_is_J_on_pos (F : ℝ → ℝ)
  (hF : CostUniqueness.UniqueCostAxioms F) :
  ∀ {x : ℝ}, 0 < x → F x = Jcost x :=
  IndisputableMonolith.CostUniqueness.unique_cost_on_pos F hF

/-- Specialization for Jcost itself (trivial equality, exported for symmetry). -/
@[simp] theorem Jcost_equals_J_on_pos :
  ∀ {x : ℝ}, 0 < x → Jcost x = Jcost x := by
  intro _ _; rfl

end CPMBridge
end Verification
end IndisputableMonolith
