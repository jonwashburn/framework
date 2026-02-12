import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

open scoped Distributions

namespace ScratchStructureMapComp

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

-- CurryRight equivalence as a CLM between fiber targets for (j+1)-derivatives
noncomputable def curryRightCLM (j : ℕ) :
    (E [×(j+1)]→L[ℝ] F) →L[ℝ] (E [×j]→L[ℝ] (E →L[ℝ] F)) :=
  ((continuousMultilinearCurryRightEquiv' ℝ j E F).toContinuousLinearEquiv :
      (E [×(j+1)]→L[ℝ] F) ≃L[ℝ] (E [×j]→L[ℝ] (E →L[ℝ] F)))

-- The expected key identity at the level of structure maps
-- structureMapCLM j (fderivLM f) = (BoundedContinuousFunction.comp (curryRightCLM j) ?) (structureMapCLM (j+1) f)

#check ContDiffMapSupportedIn.structureMapCLM
#check ContDiffMapSupportedIn.postcompCLM

end ScratchStructureMapComp
