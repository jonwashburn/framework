import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

open scoped Distributions

namespace ScratchFderivStructureMapIdentity

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

noncomputable def curryRightCLM (j : ℕ) :
    (E [×(j+1)]→L[ℝ] F) →L[ℝ] (E [×j]→L[ℝ] (E →L[ℝ] F)) :=
  ((continuousMultilinearCurryRightEquiv' ℝ j E F).toContinuousLinearEquiv :
      (E [×(j+1)]→L[ℝ] F) ≃L[ℝ] (E [×j]→L[ℝ] (E →L[ℝ] F)))

-- The key pointwise identity: iterated derivative of fderiv equals curryRight of higher iterated derivative
private theorem iteratedFDeriv_fderiv_eq_curryRight (f : E → F) (x : E) (j : ℕ) :
    iteratedFDeriv ℝ j (fun y => fderiv ℝ f y) x =
      (continuousMultilinearCurryRightEquiv' ℝ j E F) (iteratedFDeriv ℝ (j+1) f x) := by
  have h := (iteratedFDeriv_succ_eq_comp_right (𝕜 := ℝ) (f := f) (x := x) (n := j))
  have h' := congrArg (continuousMultilinearCurryRightEquiv' ℝ j E F) h
  simpa [Function.comp] using h'.symm

-- Show the structure map identity on 𝓓_K
lemma structureMapCLM_comp_fderivLM (j : ℕ) (f : 𝓓_{K}(E, F)) :
    structureMapCLM (𝕜 := ℝ) (n := (⊤ : ℕ∞)) (K := K) j (fderivLM (E := E) (F := F) (K := K) f)
      =
    -- apply curryRight to the (j+1)-structure map
    BoundedContinuousFunction.comp (curryRightCLM (E := E) (F := F) j)
      (ContinuousLinearMap.lipschitz (curryRightCLM (E := E) (F := F) j))
      (structureMapCLM (𝕜 := ℝ) (n := (⊤ : ℕ∞)) (K := K) (j+1) f) := by
  -- ext on x and multilinear argument
  ext x v
  -- unfold structureMapCLM_apply
  simp [structureMapCLM_apply, fderivLM, curryFin1CLM, curryRightCLM, iteratedFDeriv_fderiv_eq_curryRight]

end ScratchFderivStructureMapIdentity
