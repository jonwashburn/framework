import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Distribution.TestFunction

open scoped Distributions

namespace ScratchTestFunctionComplex2

open Classical TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
#check (inferInstance : NormedSpace ℝ E)

variable {Ω : TopologicalSpace.Opens E}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
#check (inferInstance : NormedSpace ℝ F)

#check 𝓓(Ω, F)

end ScratchTestFunctionComplex2
