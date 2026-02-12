import Mathlib
import IndisputableMonolith.Relativity/ILG/FRW

namespace IndisputableMonolith
namespace Relativity
namespace ILG

/-- Placeholder growth index f = d ln δ / d ln a (symbolic). -/
noncomputable def growth_index (δ a : ℝ) : ℝ := δ / a

@[simp] theorem growth_index_pos_of (δ a : ℝ) (ha : 0 < a) (hδ : 0 < δ) :
  0 < growth_index δ a := by
  simp [growth_index, div_pos hδ ha]

/-- Growth factor from effective weight w(k,a) (scaffold). -/
noncomputable def growth_from_w (w : ℝ → ℝ → ℝ) (k a : ℝ) : ℝ :=
  a * w k a

theorem growth_from_w_positive (w : ℝ → ℝ → ℝ) (k a : ℝ)
    (ha : 0 < a) (hw : 0 < w k a) :
  0 < growth_from_w w k a := by
  simp [growth_from_w]
  exact mul_pos ha hw

end ILG
end Relativity
end IndisputableMonolith
