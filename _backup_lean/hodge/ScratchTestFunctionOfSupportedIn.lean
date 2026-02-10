import Mathlib.Analysis.Distribution.TestFunction

open scoped Distributions

namespace ScratchTestFunctionOfSupportedIn

open Classical TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Ω : TopologicalSpace.Opens E}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {n : ℕ∞}
variable {K : Compacts E}

#check TestFunction.ofSupportedIn
#check TestFunction.ofSupportedInLM
#check TestFunction.ofSupportedInCLM
#check TestFunction.ofSupportedInContinuousLinearMap

end ScratchTestFunctionOfSupportedIn
