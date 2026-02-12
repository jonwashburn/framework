import Mathlib
import IndisputableMonolith.Constants
-- Interval import removed: not used here, bounds are axiomatized

namespace IndisputableMonolith
namespace Constants

noncomputable def w8_from_eight_tick : ℝ := 2.488254397846

noncomputable def f_gap : ℝ := w8_from_eight_tick * Real.log phi

def fGapLowerBound : ℚ := 2993443258792019287026689 / 2500000000000000000000000
def fGapUpperBound : ℚ := 5986887286510633232418913 / 5000000000000000000000000

/-- Hypothesis for the certified numerical bounds for the gap weight.
    Converted from axiom - unused in proofs, requires interval arithmetic to prove. -/
def f_gap_bounds_hypothesis : Prop :=
  ((fGapLowerBound : ℚ) : ℝ) < f_gap ∧ f_gap < ((fGapUpperBound : ℚ) : ℝ)

end Constants
end IndisputableMonolith
