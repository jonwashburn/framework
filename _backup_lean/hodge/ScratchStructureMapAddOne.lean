import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

open scoped Distributions

namespace ScratchStructureMapAddOne

open Classical TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {K : Compacts E}

open ContDiffMapSupportedIn

-- Curry the (j+1)-multilinear map into a j-multilinear map with values in E→L F
noncomputable def curryRightCLM (j : ℕ) :
    (E [×(j+1)]→L[ℝ] F) →L[ℝ] (E [×j]→L[ℝ] (E →L[ℝ] F)) :=
  ((continuousMultilinearCurryRightEquiv' ℝ j E F).toContinuousLinearEquiv :
      (E [×(j+1)]→L[ℝ] F) ≃L[ℝ] (E [×j]→L[ℝ] (E →L[ℝ] F)))

-- A lemma relating iteratedFDeriv (j+1) with curryRightEquiv and iteratedFDeriv j of fderiv
#check iteratedFDeriv_succ_eq_comp_right

end ScratchStructureMapAddOne
