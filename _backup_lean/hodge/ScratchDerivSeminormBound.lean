import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn

open scoped Distributions

namespace ScratchDerivSeminormBound

open Classical TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {K : Compacts E}

open ContDiffMapSupportedIn

#check ContDiffMapSupportedIn.seminorm
#check ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm
#check ContDiffMapSupportedIn.structureMapCLM

-- Any lemma about seminorm of iteratedFDerivLM?
#check ContDiffMapSupportedIn.seminorm_iteratedFDerivLM_le
#check ContDiffMapSupportedIn.seminorm_iteratedFDerivLM

end ScratchDerivSeminormBound
