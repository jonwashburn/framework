import Mathlib.Analysis.Distribution.TestFunction

open scoped Distributions

namespace ScratchStage1d

open Classical TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {K : Compacts E}

#check 𝓓_{K}(E, F)
#check TopologicalSpace (𝓓_{K}(E, F))
#check ContinuousLinearMap
#check (𝓓_{K}(E, F) →L[ℝ] 𝓓_{K}(E, F))

#check ContDiffMapSupportedIn.iteratedFDerivLM
#check ContDiffMapSupportedIn.iteratedFDeriv

end ScratchStage1d
