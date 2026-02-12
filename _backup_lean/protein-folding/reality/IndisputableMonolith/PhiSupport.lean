import Mathlib
import Mathlib.NumberTheory.Real.GoldenRatio
import IndisputableMonolith.Constants

namespace IndisputableMonolith
namespace PhiSupport

open Real

/-- Closed form for φ. -/
lemma phi_def : Constants.phi = Real.goldenRatio := rfl

/-- φ > 1 (proved from Mathlib's goldenRatio facts). -/
theorem one_lt_phi : (1 : ℝ) < Constants.phi := by simp [phi_def, Real.one_lt_goldenRatio]

/-- φ ≠ 0 (consequence of φ > 1). -/
lemma phi_ne_zero : Constants.phi ≠ 0 := ne_of_gt (lt_trans (by norm_num : (0 : ℝ) < 1) one_lt_phi)

/-- φ² = φ + 1 (the defining quadratic, proved from Mathlib). -/
@[simp] theorem phi_squared : Constants.phi ^ 2 = Constants.phi + 1 := by
  simp [phi_def, Real.goldenRatio_sq]

/-- φ = 1 + 1/φ as an algebraic corollary. -/
theorem phi_fixed_point : Constants.phi = 1 + Constants.phi⁻¹ := by
  have h_sq : Constants.phi ^ 2 = Constants.phi + 1 := phi_squared
  have h_ne_zero : Constants.phi ≠ 0 := phi_ne_zero
  calc
    Constants.phi = (Constants.phi ^ 2) / Constants.phi := by
      rw [pow_two, mul_div_cancel_left₀ _ h_ne_zero]
    _ = (Constants.phi + 1) / Constants.phi := by rw [h_sq]
    _ = Constants.phi / Constants.phi + 1 / Constants.phi := by rw [add_div]
    _ = 1 + 1 / Constants.phi := by rw [div_self h_ne_zero]
    _ = 1 + Constants.phi⁻¹ := by rw [one_div]

end PhiSupport
end IndisputableMonolith
