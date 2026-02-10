import Mathlib.Analysis.Distribution.TestFunction

open scoped Distributions

namespace ScratchTestFunctionComp

open Classical TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Ω : TopologicalSpace.Opens E}
variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

#check TestFunction.postcompCLM
#check ContinuousLinearMap.comp

end ScratchTestFunctionComp
