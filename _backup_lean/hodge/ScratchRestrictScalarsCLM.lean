import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Basic

namespace ScratchRestrictScalarsCLM

open Classical

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

#check ContinuousLinearMap.restrictScalars
#check ContinuousLinearMap.restrictScalarsₗ
#check ContinuousLinearMap.restrictScalarsₗᵢ

end ScratchRestrictScalarsCLM
