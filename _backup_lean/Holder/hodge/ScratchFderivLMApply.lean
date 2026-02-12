import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

open scoped Distributions

namespace ScratchFderivLMApply

open Classical TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {K : Compacts E}

open ContDiffMapSupportedIn

noncomputable def curryFin1CLM : (E [×1]→L[ℝ] F) →L[ℝ] (E →L[ℝ] F) :=
  ((continuousMultilinearCurryFin1 ℝ E F).toContinuousLinearEquiv :
      (E [×1]→L[ℝ] F) ≃L[ℝ] (E →L[ℝ] F))

noncomputable def fderivLM : 𝓓_{K}(E, F) →ₗ[ℝ] 𝓓_{K}(E, E →L[ℝ] F) :=
  (ContDiffMapSupportedIn.postcompLM (n := (⊤ : ℕ∞)) (K := K) (𝕜 := ℝ)
      (T := curryFin1CLM (E := E) (F := F)))
    ∘ₗ (ContDiffMapSupportedIn.iteratedFDerivLM (𝕜 := ℝ) (E := E) (F := F) (K := K) 1)

lemma fderivLM_apply (f : 𝓓_{K}(E, F)) :
    fderivLM (E := E) (F := F) (K := K) f =
      (curryFin1CLM (E := E) (F := F)) ∘ (iteratedFDeriv ℝ 1 f) := by
  -- ext on x
  ext x
  -- unfold and simp
  simp [fderivLM, curryFin1CLM]

end ScratchFderivLMApply
