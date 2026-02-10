import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

open scoped Distributions

namespace ScratchIteratedFDerivLMContinuous

open Classical TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {K : Compacts E}

open ContDiffMapSupportedIn

-- First we build the CLM `fderivCLM : 𝓓_K(E,F) →L 𝓓_K(E,E→L F)`.

noncomputable def curryFin1CLM : (E [×1]→L[ℝ] F) →L[ℝ] (E →L[ℝ] F) :=
  ((continuousMultilinearCurryFin1 ℝ E F).toContinuousLinearEquiv :
      (E [×1]→L[ℝ] F) ≃L[ℝ] (E →L[ℝ] F))

noncomputable def fderivLM : 𝓓_{K}(E, F) →ₗ[ℝ] 𝓓_{K}(E, E →L[ℝ] F) :=
  (ContDiffMapSupportedIn.postcompLM (n := (⊤ : ℕ∞)) (K := K) (𝕜 := ℝ)
      (T := curryFin1CLM (E := E) (F := F)))
    ∘ₗ (ContDiffMapSupportedIn.iteratedFDerivLM (𝕜 := ℝ) (E := E) (F := F) (K := K) 1)

-- Key lemma: relate iterated derivatives of fderiv to higher iterated derivatives via curryRight
private theorem iteratedFDeriv_fderiv_eq_curryRight (f : E → F) (x : E) (j : ℕ) :
    iteratedFDeriv ℝ j (fun y => fderiv ℝ f y) x =
      (continuousMultilinearCurryRightEquiv' ℝ j E F) (iteratedFDeriv ℝ (j+1) f x) := by
  have h := (iteratedFDeriv_succ_eq_comp_right (𝕜 := ℝ) (f := f) (x := x) (n := j))
  have h' := congrArg (continuousMultilinearCurryRightEquiv' ℝ j E F) h
  simpa [Function.comp] using h'.symm

-- Now prove continuity using the universal property of the topology: continuous_iff_comp.

theorem continuous_fderivLM : Continuous (fderivLM (E := E) (F := F) (K := K)) := by
  -- Use continuity_iff_comp on the codomain 𝓓_K(E,E→L F)
  -- We'll show: for all j, structureMapCLM ∘ fderivLM is continuous.
  refine (ContDiffMapSupportedIn.continuous_iff_comp (n := (⊤ : ℕ∞)) (K := K)
    (φ := fderivLM (E := E) (F := F) (K := K))).2 ?_
  intro j
  -- show continuity of structureMapCLM ℝ ⊤ j ∘ fderivLM
  -- We'll prove it's equal to postcomp by curryRightCLM of structureMapCLM ℝ ⊤ (j+1)
  --
  -- TODO: finish
  admit

end ScratchIteratedFDerivLMContinuous
