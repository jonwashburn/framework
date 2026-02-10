import Hodge.Basic
import Mathlib.Analysis.Complex.Basic

namespace ScratchAltRealInput

open Classical

variable {n k : ℕ}

-- Can we view the alternatization map as taking ℝ-linear maps?
#check (ContinuousLinearMap.restrictScalars (R := ℝ)
  (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℂ (TangentModel n) ℂ (n := k)))

-- What is its domain?
#check ((ContinuousLinearMap.restrictScalars (R := ℝ)
  (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℂ (TangentModel n) ℂ (n := k))).toLinearMap)

end ScratchAltRealInput
