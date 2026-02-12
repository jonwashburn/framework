import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

namespace ScratchCurryAssoc

open Classical

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

-- Search for an equivalence between (E[×(i+j)]→L F) and (E[×j]→L (E[×i]→L F))
#check ContinuousMultilinearMap.curryRightEquiv
#check ContinuousMultilinearMap.curryMidEquiv

end ScratchCurryAssoc
