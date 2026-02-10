import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

open scoped Distributions

namespace ScratchdCLMContinuity2

open Classical TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Ω : TopologicalSpace.Opens E}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {K : Compacts E}

noncomputable def curryFin1CLM : (E [×1]→L[ℝ] F) →L[ℝ] (E →L[ℝ] F) :=
  ((continuousMultilinearCurryFin1 ℝ E F).toContinuousLinearEquiv :
      (E [×1]→L[ℝ] F) ≃L[ℝ] (E →L[ℝ] F))

noncomputable def fderivLM : 𝓓_{K}(E, F) →ₗ[ℝ] 𝓓_{K}(E, E →L[ℝ] F) :=
  (ContDiffMapSupportedIn.postcompLM (n := (⊤ : ℕ∞)) (K := K) (𝕜 := ℝ)
      (T := curryFin1CLM (E := E) (F := F)))
    ∘ₗ (ContDiffMapSupportedIn.iteratedFDerivLM (𝕜 := ℝ) (E := E) (F := F) (K := K) 1)

#check fderivLM (E := E) (F := F) (K := K)

end ScratchdCLMContinuity2
