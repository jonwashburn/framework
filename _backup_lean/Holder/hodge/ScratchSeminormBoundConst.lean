import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn

open scoped Distributions

namespace ScratchSeminormBoundConst

open Classical TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {K : Compacts E}

open ContDiffMapSupportedIn

variable (f : 𝓓_{K}(E, F))

-- Check the type of the seminorm notation
#check (N[ℝ; F]_{K, 0} : Seminorm ℝ (𝓓_{K}(E, F)))

end ScratchSeminormBoundConst
