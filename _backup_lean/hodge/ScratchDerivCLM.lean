import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

open scoped Distributions

namespace ScratchDerivCLM

open Classical TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Ω : TopologicalSpace.Opens E}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

abbrev DerivTarget := E →L[ℝ] F

noncomputable def curryFin1CLM :
    (E [×1]→L[ℝ] F) →L[ℝ] DerivTarget (E := E) (F := F) :=
  ((continuousMultilinearCurryFin1 ℝ E F).toContinuousLinearEquiv :
      (E [×1]→L[ℝ] F) ≃L[ℝ] DerivTarget (E := E) (F := F))

noncomputable def fderivTestFunction (f : 𝓓(Ω, F)) : 𝓓(Ω, DerivTarget (E := E) (F := F)) := by
  classical
  -- Start from the 1st iterated derivative (as a test function)
  let g : 𝓓(Ω, E [×1]→L[ℝ] F) := by
    -- `TestFunction.mk` constructor style
    refine
      { toFun := fun x => iteratedFDeriv ℝ 1 (f : E → F) x
        contDiff' := ?_
        hasCompactSupport' := ?_
        tsupport_subset' := ?_ }
    · -- smooth
      have hi : ((1 : ℕ) : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) :=
        (WithTop.coe_le_coe).2 (le_top : (1 : ℕ∞) ≤ ⊤)
      simpa using (f.contDiff.of_le hi).iteratedFDeriv_right (m := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) (i := 1) (by
        simpa using (le_rfl : (↑(⊤ : ℕ∞) : WithTop ℕ∞) + (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞)))
    · simpa using (f.hasCompactSupport.iteratedFDeriv (𝕜 := ℝ) (n := 1))
    ·
      refine (tsupport_iteratedFDeriv_subset (𝕜 := ℝ) (n := 1) (f := (f : E → F))).trans ?_
      exact f.tsupport_subset
  -- Postcompose by the curry map
  exact (TestFunction.postcompCLM (n := (⊤ : ℕ∞)) (Ω := Ω) (𝕜 := ℝ) (F := (E [×1]→L[ℝ] F))
    (F' := DerivTarget (E := E) (F := F)) (curryFin1CLM (E := E) (F := F))) g

end ScratchDerivCLM
