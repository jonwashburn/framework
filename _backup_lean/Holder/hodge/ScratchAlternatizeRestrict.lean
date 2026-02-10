import Hodge.Basic
import Mathlib.Analysis.Complex.Basic

namespace ScratchAlternatizeRestrict

open Classical

variable {n k : ℕ}

-- The ℂ-linear alternatization CLM
#check (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℂ (TangentModel n) ℂ (n := k))

-- Try to restrict scalars to ℝ
noncomputable def altCLM_real :
    (TangentModel n →L[ℝ] FiberAlt n k) →L[ℝ] (TangentModel n [⋀^Fin (k+1)]→L[ℂ] ℂ) := by
  -- This won't typecheck yet; we want to see the required type.
  exact (ContinuousLinearMap.restrictScalars ℂ (R := ℝ)
    (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℂ (TangentModel n) ℂ (n := k)))

end ScratchAlternatizeRestrict
