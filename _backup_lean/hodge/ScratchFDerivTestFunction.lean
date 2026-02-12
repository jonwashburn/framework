import Mathlib.Analysis.Distribution.TestFunction

open scoped Distributions

namespace ScratchFDerivTestFunction

open Classical TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Ω : TopologicalSpace.Opens E}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

variable (f : 𝓓(Ω, F))

-- Does fderiv of f land in 𝓓(Ω, E→L F) ?
#check fderiv ℝ (f : E → F)
#check ContDiffMapSupportedIn.fderiv

end ScratchFDerivTestFunction
