import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn

open scoped Distributions

namespace ScratchOfSupportSubsetSig

open Classical TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {K : Compacts E}

#check ContDiffMapSupportedIn.of_support_subset

end ScratchOfSupportSubsetSig
