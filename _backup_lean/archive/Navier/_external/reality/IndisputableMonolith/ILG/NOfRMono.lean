import Mathlib
import IndisputableMonolith.ILG.ParamsKernel

namespace IndisputableMonolith
namespace ILG

noncomputable section

/-- Internal guard to keep square-roots well-defined (WIP stub). -/
noncomputable def εr : ℝ := 1e-12

/-– Analytic global radial shape factor: reuse canonical def. -/
@[simp] noncomputable def n_of_r (A r0 p : ℝ) (r : ℝ) : ℝ :=
  IndisputableMonolith.ILG.n_of_r A r0 p r

/-- Monotonicity in A under nonnegative exponent (delegates to canonical proof). -/
lemma n_of_r_mono_A_of_nonneg_p {A1 A2 r0 p r : ℝ}
  (hp : 0 ≤ p) (hA12 : A1 ≤ A2) :
  n_of_r A1 r0 p r ≤ n_of_r A2 r0 p r := by
  dsimp [n_of_r]
  exact IndisputableMonolith.ILG.n_of_r_mono_A_of_nonneg_p (hp:=hp) (hA12:=hA12)

end
end ILG
end IndisputableMonolith
