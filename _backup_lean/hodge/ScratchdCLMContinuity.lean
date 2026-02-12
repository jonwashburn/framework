import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

open scoped Distributions

namespace ScratchdCLMContinuity

open Classical TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Ω : TopologicalSpace.Opens E}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

-- We'll try to define the first derivative CLM on 𝓓_K and see if it typechecks.
variable {K : Compacts E}

-- Candidate fderiv linear map (already in ContDiffMapSupportedIn file)
#check ContDiffMapSupportedIn.iteratedFDerivLM

-- We can postcompose by curryFin1CLM (as a fiber map) to get into E→L F
noncomputable def curryFin1CLM : (E [×1]→L[ℝ] F) →L[ℝ] (E →L[ℝ] F) :=
  ((continuousMultilinearCurryFin1 ℝ E F).toContinuousLinearEquiv :
      (E [×1]→L[ℝ] F) ≃L[ℝ] (E →L[ℝ] F))

-- Compose: 𝓓_K(E,F) -> 𝓓_K(E, E[×1]→L F) via iteratedFDerivLM, then postcomp to curry
noncomputable def fderivLM : 𝓓_{K}(E, F) →ₗ[ℝ] 𝓓_{K}(E, E →L[ℝ] F) :=
  (ContDiffMapSupportedIn.postcompLM (n := (⊤ : ℕ∞)) (K := K) (T := curryFin1CLM (E := E) (F := F)) ℝ)
    ∘ₗ (ContDiffMapSupportedIn.iteratedFDerivLM (𝕜 := ℝ) (E := E) (F := F) (K := K) 1)

#check fderivLM (E := E) (F := F) (K := K)

end ScratchdCLMContinuity
