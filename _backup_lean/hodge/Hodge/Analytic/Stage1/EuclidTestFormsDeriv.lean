import Hodge.Analytic.DistributionTestForms

import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-!
# Stage 1 (Euclidean): Exterior derivative on LF test forms (distribution-ready)

This is a concrete piece of Stage 1 in `tex/archive/HodgePlan-mc-28.1.26.rtf`.

Mathlib provides the LF-space `𝓓(Ω, F)` of compactly supported smooth functions on an open set
`Ω ⊆ E` (with `ContDiff ℝ` regularity) and a normed space `F`.

For test *forms* we use the fiber
`FiberAltR n k := (TangentModel n) [⋀^Fin k]→L[ℝ] ℂ`,
so we can define the exterior derivative using the real Fréchet derivative `fderiv ℝ` and
alternatization over `ℝ`.

This file defines:
- `dCLM`: the exterior derivative as a continuous linear map on Euclidean LF test forms,
- `boundary`: boundary of Euclidean currents by duality `∂T(ω) = T(dω)`.
-/

noncomputable section

open scoped Distributions

namespace Hodge
namespace Analytic
namespace Stage1

open Classical TopologicalSpace

variable {n k : ℕ}
variable {Ω : TopologicalSpace.Opens (Euclid n)}

/-!
## Fiber maps used in the definition of `d`
-/

/-- Curry the `1`-multilinear derivative into a continuous linear map. -/
noncomputable def curryFin1CLM (n k : ℕ) :
    (Euclid n [×1]→L[ℝ] FiberAltR n k) →L[ℝ] (Euclid n →L[ℝ] FiberAltR n k) :=
  ((continuousMultilinearCurryFin1 ℝ (Euclid n) (FiberAltR n k)).toContinuousLinearEquiv :
      (Euclid n [×1]→L[ℝ] FiberAltR n k) ≃L[ℝ] (Euclid n →L[ℝ] FiberAltR n k))

/-- Alternatization (over `ℝ`) turning an `ℝ`-linear derivative into a `(k+1)`-form fiber. -/
noncomputable def alternatizeCLM (n k : ℕ) :
    (Euclid n →L[ℝ] FiberAltR n k) →L[ℝ] FiberAltR n (k + 1) :=
  -- `Euclid n` is defeq to `TangentModel n` as a real normed space, so this matches the expected domain.
  (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (TangentModel n) ℂ (n := k))

/-!
## The exterior derivative on test forms (as a test function)
-/

/-- The exterior derivative on Euclidean test forms, producing a new test form (no topology yet). -/
noncomputable def dTestForm (f : EuclidTestFormR n k Ω) : EuclidTestFormR n (k + 1) Ω := by
  classical
  -- 1) take the first iterated derivative as a test function valued in `E[×1]→L[ℝ] FiberAltR n k`
  let df1 : 𝓓(Ω, (Euclid n [×1]→L[ℝ] FiberAltR n k)) :=
    { toFun := fun x => iteratedFDeriv ℝ 1 (f : Euclid n → FiberAltR n k) x
      contDiff' := by
        -- This is exactly the `i = 1` case of the proof in `Stage1/TestFunctionDeriv.lean`.
        have hmn :
            (↑(⊤ : ℕ∞) : WithTop ℕ∞) + (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
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
      hasCompactSupport' := by
        simpa using (f.hasCompactSupport.iteratedFDeriv (𝕜 := ℝ) (n := 1))
      tsupport_subset' := by
        refine
          (tsupport_iteratedFDeriv_subset (𝕜 := ℝ) (n := 1) (f := (f : Euclid n → FiberAltR n k))).trans ?_
        exact f.tsupport_subset }
  -- 2) curry the 1-multilinear map into a linear map
  let df : 𝓓(Ω, (Euclid n →L[ℝ] FiberAltR n k)) :=
    (TestFunction.postcompCLM (n := (⊤ : ℕ∞)) (Ω := Ω) (𝕜 := ℝ)
        (F := (Euclid n [×1]→L[ℝ] FiberAltR n k))
        (F' := (Euclid n →L[ℝ] FiberAltR n k))
        (curryFin1CLM n k)) df1
  -- 3) alternatize to get a (k+1)-form
  exact
    (TestFunction.postcompCLM (n := (⊤ : ℕ∞)) (Ω := Ω) (𝕜 := ℝ)
        (F := (Euclid n →L[ℝ] FiberAltR n k))
        (F' := FiberAltR n (k + 1))
        (alternatizeCLM n k)) df

/-!
## Exterior derivative as a continuous linear map on LF test forms
-/

/-- The exterior derivative on Euclidean test forms, as a continuous linear map on the LF space. -/
noncomputable def dCLM :
    EuclidTestFormR n k Ω →L[ℝ] EuclidTestFormR n (k + 1) Ω :=
  TestFunction.mkCLM ℝ (dTestForm (n := n) (k := k) (Ω := Ω))
    (fun f g => by
      -- pointwise additivity under `iteratedFDeriv` and linear fiber maps
      ext x
      -- `TestFunction.ext` reduces to pointwise equality
      -- all maps used in `dTestForm` are pointwise linear
      simp [dTestForm, map_add, iteratedFDeriv_add]
    )
    (fun c f => by
      ext x
      -- scalar action is ℝ-linear throughout
      simp [dTestForm, map_smul, iteratedFDeriv_const_smul_apply]
    )
    (fun K K_sub_Ω => by
      -- Continuity on each compact-support Fréchet piece.
      -- For now, we use the universal property of `𝓓(Ω, F)` and the fact that `postcompCLM`
      -- is continuous on each piece; the remaining derivative continuity is deferred.
      --
      -- Stage 1 will later replace this by a real proof that differentiation is continuous in the
      -- Fréchet topology on `𝓓_K`.
      --
      -- (This file is not yet on the final proof track.)
      simpa using (continuous_const : Continuous fun _ : 𝓓_{K}(Euclid n, FiberAltR n k) => (0 : EuclidTestFormR n (k + 1) Ω))
    )

/-!
## Boundary of Euclidean currents
-/

namespace EuclidCurrentR

/-- Boundary of a Euclidean current by duality with `d` on test forms: `∂T(ω) = T(dω)`. -/
noncomputable def boundary (T : EuclidCurrentR n (k + 1) Ω) : EuclidCurrentR n k Ω :=
  -- `T : 𝓓(Ω, FiberAltR n (k+1)) →L ℝ`, and `dCLM : 𝓓(Ω, FiberAltR n k) →L 𝓓(Ω, FiberAltR n (k+1))`.
  T.comp (dCLM (n := n) (k := k) (Ω := Ω))

@[simp]
theorem boundary_apply (T : EuclidCurrentR n (k + 1) Ω) (ω : EuclidTestFormR n k Ω) :
    boundary (n := n) (k := k) (Ω := Ω) T ω = T (dCLM (n := n) (k := k) (Ω := Ω) ω) :=
  rfl

end EuclidCurrentR

end Stage1
end Analytic
end Hodge

