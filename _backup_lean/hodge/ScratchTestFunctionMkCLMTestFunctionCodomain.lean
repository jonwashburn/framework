import Mathlib.Analysis.Distribution.TestFunction

open scoped Distributions

namespace ScratchTestFunctionMkCLMTestFunctionCodomain

open Classical TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Ω : TopologicalSpace.Opens E}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

#check (inferInstance : TopologicalSpace (𝓓(Ω, G)))
#check (inferInstance : IsTopologicalAddGroup (𝓓(Ω, G)))
#check (inferInstance : LocallyConvexSpace ℝ (𝓓(Ω, G)))

end ScratchTestFunctionMkCLMTestFunctionCodomain
