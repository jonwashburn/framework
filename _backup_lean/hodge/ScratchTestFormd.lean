import Hodge.Basic
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

open scoped Distributions

namespace ScratchTestFormd

open Classical TopologicalSpace

abbrev Euclid (n : ℕ) := EuclideanSpace ℂ (Fin n)

abbrev FiberAltR (n : ℕ) (k : ℕ) := (TangentModel n) [⋀^Fin k]→L[ℝ] ℂ

abbrev EuclidTestFormR (n : ℕ) (k : ℕ) (Ω : TopologicalSpace.Opens (Euclid n)) :=
  𝓓(Ω, FiberAltR n k)

namespace Stage1

variable {n k : ℕ}
variable {Ω : TopologicalSpace.Opens (Euclid n)}

noncomputable def curryFin1CLM (n k : ℕ) :
    (Euclid n [×1]→L[ℝ] FiberAltR n k) →L[ℝ] (Euclid n →L[ℝ] FiberAltR n k) :=
  ((continuousMultilinearCurryFin1 ℝ (Euclid n) (FiberAltR n k)).toContinuousLinearEquiv :
      (Euclid n [×1]→L[ℝ] FiberAltR n k) ≃L[ℝ] (Euclid n →L[ℝ] FiberAltR n k))

noncomputable def altCLM (n k : ℕ) :
    (Euclid n →L[ℝ] FiberAltR n k) →L[ℝ] FiberAltR n (k+1) :=
  (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (TangentModel n) ℂ (n := k))

/-- Pointwise exterior derivative on Euclidean test forms, as a test function. -/
noncomputable def dTestForm (f : EuclidTestFormR n k Ω) : EuclidTestFormR n (k+1) Ω := by
  classical
  -- Take the iterated derivative as a test function (values in E[×1]→L F)
  let df1 : 𝓓(Ω, (Euclid n [×1]→L[ℝ] FiberAltR n k)) := by
    -- reuse the constructor pattern (as in Hodge.Analytic.Stage1.iteratedFDerivTestFunction)
    refine
      { toFun := fun x => iteratedFDeriv ℝ 1 (f : Euclid n → FiberAltR n k) x
        contDiff' := ?_
        hasCompactSupport' := ?_
        tsupport_subset' := ?_ }
    · -- smoothness
      -- Use the existing lemma for iterated derivatives of smooth functions
      have hmn : (↑(⊤ : ℕ∞) : WithTop ℕ∞) + (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
        -- similar proof as in TestFunctionDeriv
        have hadd :
            (↑(⊤ : ℕ∞) : WithTop ℕ∞) + (↑(1 : ℕ∞) : WithTop ℕ∞) =
              (↑((⊤ : ℕ∞) + (1 : ℕ∞)) : WithTop ℕ∞) := by
          simpa [WithTop.coe_add] using (WithTop.coe_add (⊤ : ℕ∞) (1 : ℕ∞)).symm
        have hcoe :
            (↑((⊤ : ℕ∞) + (1 : ℕ∞)) : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
          exact (WithTop.coe_le_coe).2 (by simpa using (le_rfl : (⊤ : ℕ∞) ≤ ⊤))
        calc
          (↑(⊤ : ℕ∞) : WithTop ℕ∞) + (1 : WithTop ℕ∞)
              = (↑(⊤ : ℕ∞) : WithTop ℕ∞) + (↑(1 : ℕ∞) : WithTop ℕ∞) := by simp
          _ ≤ (↑((⊤ : ℕ∞) + (1 : ℕ∞)) : WithTop ℕ∞) := le_of_eq hadd
          _ ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := hcoe
      exact f.contDiff.iteratedFDeriv_right (m := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) (i := 1) (by
        simpa using hmn)
    · simpa using (f.hasCompactSupport.iteratedFDeriv (𝕜 := ℝ) (n := 1))
    ·
      refine (tsupport_iteratedFDeriv_subset (𝕜 := ℝ) (n := 1) (f := (f : Euclid n → FiberAltR n k))).trans ?_
      exact f.tsupport_subset
  -- Curry the multilinear derivative into a linear derivative
  let df : 𝓓(Ω, (Euclid n →L[ℝ] FiberAltR n k)) :=
    (TestFunction.postcompCLM (n := (⊤ : ℕ∞)) (Ω := Ω) (𝕜 := ℝ)
      (F := (Euclid n [×1]→L[ℝ] FiberAltR n k))
      (F' := (Euclid n →L[ℝ] FiberAltR n k))
      (curryFin1CLM n k)) df1
  -- Alternatize
  exact (TestFunction.postcompCLM (n := (⊤ : ℕ∞)) (Ω := Ω) (𝕜 := ℝ)
      (F := (Euclid n →L[ℝ] FiberAltR n k))
      (F' := FiberAltR n (k+1))
      (altCLM n k)) df

end Stage1

end ScratchTestFormd
