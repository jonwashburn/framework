import Mathlib.Analysis.Distribution.TestFunction

open scoped Distributions

namespace ScratchStage1e

open Classical TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Ω : TopologicalSpace.Opens E}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

-- does TestFunction have a derivative CLM?
#check TestFunction.deriv
#check TestFunction.derivCLM
#check TestFunction.fderiv
#check TestFunction.fderivCLM
#check TestFunction.iteratedFDerivCLM

end ScratchStage1e
