import Mathlib

/-!
Operator-norm of a restriction is bounded by the ambient operator-norm.

Setup:
  • 𝕂 ∈ {ℝ, ℂ} via `IsROrC 𝕂`
  • E a normed 𝕂–space
  • S ⊆ E a linear subspace (as `Submodule 𝕂 E`)
  • T : E →L[𝕂] E with `T(S) ⊆ S` so that `T.restrict S : S →L[𝕂] S` exists

Result:
  • opNorm_restrict_le (T S) : ‖T.restrict S‖ ≤ ‖T‖

This is a thin wrapper over the mathlib lemma `ContinuousLinearMap.opNorm_restrict_le`.
-/

namespace YM.SpectralStability.RestrictOpNorm

variable {𝕂 : Type*} [IsROrC 𝕂]
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕂 E]

open ContinuousLinearMap

theorem opNorm_restrict_le (T : E →L[𝕂] E) (S : Submodule 𝕂 E) :
    ‖T.restrict S‖ ≤ ‖T‖ := by
  simpa using (ContinuousLinearMap.opNorm_restrict_le (T:=T) (S:=S))

end YM.SpectralStability.RestrictOpNorm
