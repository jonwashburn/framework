import Mathlib.Analysis.Distribution.TestFunction

open scoped BoundedContinuousFunction

namespace ScratchCLMLipschitz

open Classical

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable (T : E →L[ℝ] F)

#check T.lipschitz
#check T.lipschitzWith

end ScratchCLMLipschitz
