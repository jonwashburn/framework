import Mathlib
import IndisputableMonolith.Numerics.Interval

namespace IndisputableMonolith
namespace Constants

noncomputable def w8_from_eight_tick : ℝ := 2.488254397846

noncomputable def f_gap : ℝ := w8_from_eight_tick * Real.log phi

def fGapLowerBound : ℚ := 2993443258792019287026689 / 2500000000000000000000000
def fGapUpperBound : ℚ := 5986887286510633232418913 / 5000000000000000000000000

/-- Stub axiom providing the certified numerical bounds for the gap weight. -/
axiom f_gap_bounds :
  ((fGapLowerBound : ℚ) : ℝ) < f_gap ∧ f_gap < ((fGapUpperBound : ℚ) : ℝ)

end Constants
end IndisputableMonolith
