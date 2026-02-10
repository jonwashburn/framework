import Hodge.Basic
import Mathlib.Analysis.Complex.Basic

namespace ScratchAlternatizeRestrict2

open Classical

variable {n k : ℕ}

noncomputable def altCLM_real :
    (TangentModel n →L[ℂ] FiberAlt n k) →L[ℝ] FiberAlt n (k+1) := by
  -- restrict scalars of the codomain of the CLM itself
  -- i.e. view a ℂ-linear CLM as an ℝ-linear CLM
  exact (ContinuousLinearMap.restrictScalars (R := ℝ)
    (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℂ (TangentModel n) ℂ (n := k)))

end ScratchAlternatizeRestrict2
