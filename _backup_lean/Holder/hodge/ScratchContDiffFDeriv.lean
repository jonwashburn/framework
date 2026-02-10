import Mathlib.Analysis.Distribution.TestFunction

namespace ScratchContDiffFDeriv

open Classical

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {f : E → F}

#check ContDiff.fderiv
#check ContDiffAt.fderiv
#check ContDiff.fderiv_right
#check ContDiff.fderiv_left

end ScratchContDiffFDeriv
