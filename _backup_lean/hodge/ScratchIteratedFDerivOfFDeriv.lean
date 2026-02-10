import Mathlib.Analysis.Distribution.TestFunction

namespace ScratchIteratedFDerivOfFDeriv

open Classical

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable (f : E → F)

#check iteratedFDeriv ℝ 0 (fun y => fderiv ℝ f y)
#check iteratedFDeriv ℝ 1 (fun y => fderiv ℝ f y)

end ScratchIteratedFDerivOfFDeriv
