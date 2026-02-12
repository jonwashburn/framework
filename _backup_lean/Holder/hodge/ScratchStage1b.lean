import Mathlib.Analysis.Distribution.TestFunction

open scoped Distributions

namespace ScratchStage1b

open Classical TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Ω : TopologicalSpace.Opens E}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

#check ContDiffMapSupportedIn.iteratedFDerivLM
#check ContDiffMapSupportedIn.iteratedFDerivCLM
#check ContDiffMapSupportedIn.structureMapCLM
#check TestFunction.ofSupportedIn

end ScratchStage1b
