import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn

open scoped Distributions

namespace ScratchStructureMapCLMApply

open Classical TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {K : Compacts E}

open ContDiffMapSupportedIn

variable (f : 𝓓_{K}(E, F))

#check structureMapCLM_apply
#check structureMapCLM_apply_withOrder

-- Try simp
example (j : ℕ) :
    structureMapCLM (𝕜 := ℝ) (n := (⊤ : ℕ∞)) (K := K) j f = iteratedFDeriv ℝ j f := by
  simpa [structureMapCLM, structureMapLM_apply] using (structureMapCLM_apply (𝕜 := ℝ) (K := K) (i := j) f)

end ScratchStructureMapCLMApply
