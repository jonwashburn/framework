import Mathlib.Analysis.Normed.Module.Multilinear.Curry

namespace ScratchLinearIsometryEquivFields

open Classical

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

variable (e : E ≃ₗᵢ[𝕜] F)

#check e.toLinearEquiv
#check e.toContinuousLinearMap
#check e.toContinuousLinearEquiv

end ScratchLinearIsometryEquivFields
