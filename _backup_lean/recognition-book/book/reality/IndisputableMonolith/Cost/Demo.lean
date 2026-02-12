import Mathlib

namespace IndisputableMonolith
namespace CostDemo

noncomputable def Gcosh (t : ℝ) : ℝ := ((Real.exp t + Real.exp (-t)) / 2 - 1)

lemma Gcosh_even : ∀ t : ℝ, Gcosh (-t) = Gcosh t := by
  intro t
  simpa [Gcosh, add_comm] using rfl

lemma Gcosh_base0 : Gcosh 0 = 0 := by
  simp [Gcosh]

end CostDemo

namespace CostDemo2

noncomputable def GcoshScaled (t : ℝ) : ℝ := (CostDemo.Gcosh t)

end CostDemo2

end IndisputableMonolith

