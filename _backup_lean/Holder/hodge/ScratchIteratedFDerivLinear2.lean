import Mathlib.Analysis.Distribution.TestFunction

namespace ScratchIteratedFDerivLinear2

open Classical

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

#check iteratedFDeriv_add
#check iteratedFDeriv_const_smul_apply

end ScratchIteratedFDerivLinear2
