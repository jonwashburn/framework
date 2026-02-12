import Mathlib.Analysis.Distribution.TestFunction

namespace ScratchContDiffIteratedSig

open Classical

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

#check ContDiff.iteratedFDeriv_right
#check ContDiff.fderiv_right

end ScratchContDiffIteratedSig
