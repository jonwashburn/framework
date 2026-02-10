import Mathlib

namespace IndisputableMonolith
namespace Cost

noncomputable def Jlog (t : ℝ) : ℝ := ((Real.exp t + Real.exp (-t)) / 2) - 1

@[simp] lemma Jlog_as_exp (t : ℝ) : Jlog t = ((Real.exp t + Real.exp (-t)) / 2) - 1 := rfl

@[simp] lemma Jlog_zero : Jlog 0 = 0 := by
  simp [Jlog]

end Cost
end IndisputableMonolith
