import Hodge.Basic
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

open scoped Distributions

namespace ScratchRealAltPipeline

open Classical TopologicalSpace

abbrev Euclid (n : ℕ) := EuclideanSpace ℂ (Fin n)

/-- Real-alternating k-linear maps on the real vector space underlying `ℂ^n`, valued in `ℂ`. -/
abbrev FiberAltR (n : ℕ) (k : ℕ) := (TangentModel n) [⋀^Fin k]→L[ℝ] ℂ

variable {n k : ℕ}
variable {Ω : TopologicalSpace.Opens (Euclid n)}

variable (f : 𝓓(Ω, FiberAltR n k))

-- First derivative as a test function valued in multilinear maps
#check iteratedFDeriv ℝ 1 (f : Euclid n → FiberAltR n k)

-- Curry to get a test function valued in linear maps
noncomputable def curryFin1CLM :
    (Euclid n [×1]→L[ℝ] FiberAltR n k) →L[ℝ] (Euclid n →L[ℝ] FiberAltR n k) :=
  ((continuousMultilinearCurryFin1 ℝ (Euclid n) (FiberAltR n k)).toContinuousLinearEquiv :
      (Euclid n [×1]→L[ℝ] FiberAltR n k) ≃L[ℝ] (Euclid n →L[ℝ] FiberAltR n k))

-- Alternatize to get (k+1)-forms
noncomputable def altCLM :
    (Euclid n →L[ℝ] FiberAltR n k) →L[ℝ] FiberAltR n (k+1) :=
  (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (TangentModel n) ℂ (n := k))

#check altCLM (n := n) (k := k)

end ScratchRealAltPipeline
