import Mathlib
import IndisputableMonolith.Ethics.Core

namespace IndisputableMonolith
namespace Ethics
namespace Decision
namespace Examples

open IndisputableMonolith.Measurement

def unitCost : CostModel Unit :=
{ cost := fun _ => (0 : ℝ)
, nonneg := by intro _; simpa }

def Punit : Policy Unit := { period := 8, threshold := 0, costModel := unitCost }

def cqLo : CQ := { listensPerSec := 1, opsPerSec := 1, coherence8 := 1
, coherence8_bounds := by
    exact And.intro (by decide) (And.intro (by decide) (by decide)) }

def cqHi : CQ := { listensPerSec := 2, opsPerSec := 1, coherence8 := 1
, coherence8_bounds := by
    exact And.intro (by decide) (And.intro (by decide) (by decide)) }

def rLo : Request Unit := { action := (), cq := cqLo }
def rHi : Request Unit := { action := (), cq := cqHi }

/-- With default-true gates and period 8 (no Gap45 gating), all requests pass filter. -/
@[simp] theorem filter_all_pass (xs : List (Request Unit)) :
  filterByGates (P:=Punit) xs = xs := by
  classical
  -- admissible holds (period=8 disables Gap45 requirement), and all gates are True
  simp [filterByGates, gatesOk, admissible, IndisputableMonolith.Gap45.requiresExperience,
        justiceOk, reciprocityOk, temperanceOk, withinWindow, uniqueInWindow, fairnessOk,
        adversarialOk, Measurement.score]

end Examples
end Decision
end Ethics
end IndisputableMonolith

