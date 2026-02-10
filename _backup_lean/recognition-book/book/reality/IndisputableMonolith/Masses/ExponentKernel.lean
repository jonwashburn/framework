import Mathlib

namespace IndisputableMonolith
namespace Masses
namespace Exponent

/-- Gauge equivalence on masses: identify by nonzero scale factors (e.g., sector gauges). -/
def GaugeEq (m₁ m₂ : ℝ) : Prop := ∃ c : ℝ, c ≠ 0 ∧ m₁ = c * m₂

@[simp] lemma gauge_refl (m : ℝ) : GaugeEq m m := ⟨1, by norm_num, by simp⟩

@[simp] lemma gauge_symm {a b : ℝ} : GaugeEq a b → GaugeEq b a := by
  intro h; rcases h with ⟨c, hc, h⟩
  refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
  -- a = c * b ⇒ b = c⁻¹ * a
  rw [h]
  simp [hc]

@[simp] lemma gauge_trans {a b c : ℝ} : GaugeEq a b → GaugeEq b c → GaugeEq a c := by
  intro h₁ h₂; rcases h₁ with ⟨x, hx, hxEq⟩; rcases h₂ with ⟨y, hy, hyEq⟩
  refine ⟨x*y, mul_ne_zero hx hy, ?_⟩
  simpa [hxEq, hyEq, mul_comm, mul_left_comm, mul_assoc]

end Exponent
end Masses
end IndisputableMonolith
