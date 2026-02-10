import Mathlib.Analysis.Normed.Module.Multilinear.Curry

namespace ScratchCurryAssoc2

open Classical

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

#check ContinuousMultilinearMap.curryMidEquiv
#check continuousMultilinearCurryRightEquiv
#check continuousMultilinearCurryRightEquiv'

end ScratchCurryAssoc2
