import Mathlib.Analysis.Distribution.TestFunction

namespace ScratchFDerivAdd

open Classical

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

#check fderiv_add
#check fderiv_smul
#check fderiv_const_smul
#check fderiv_const_smul_apply

end ScratchFDerivAdd
