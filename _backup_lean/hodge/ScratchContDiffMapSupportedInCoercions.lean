import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn

open scoped Distributions

namespace ScratchContDiffMapSupportedInCoercions

open Classical TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {K : Compacts E}

variable (f : 𝓓_{K}(E, F))

#check (f : E → F)
#check f.contDiff
#check f.tsupport_subset

end ScratchContDiffMapSupportedInCoercions
