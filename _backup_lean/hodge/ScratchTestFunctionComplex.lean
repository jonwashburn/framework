import Mathlib.Analysis.Distribution.TestFunction

open scoped Distributions

namespace ScratchTestFunctionComplex

open Classical TopologicalSpace

-- Try to use 𝓓 with E a complex normed space
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

-- does TestFunction still require NormedSpace ℝ E, so we'd need RestrictScalars?
#check (inferInstance : NormedSpace ℝ E)

variable {Ω : TopologicalSpace.Opens E}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
#check (inferInstance : NormedSpace ℝ F)

-- Can we form 𝓓(Ω,F) ?
#check 𝓓(Ω, F)

end ScratchTestFunctionComplex
