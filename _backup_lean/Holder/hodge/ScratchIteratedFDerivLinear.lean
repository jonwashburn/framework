import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

namespace ScratchIteratedFDerivLinear

open Classical

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

#check iteratedFDeriv_add
#check iteratedFDeriv_const_smul_apply
#check iteratedFDeriv_succ_eq_comp_right

end ScratchIteratedFDerivLinear
