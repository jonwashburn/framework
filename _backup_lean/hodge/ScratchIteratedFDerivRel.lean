import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

namespace ScratchIteratedFDerivRel

open Classical

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable (f : E → F) (x : E) (j : ℕ)

-- Curry-right equiv between E[×(j+1)]→L F and E[×j]→L (E→L F)
#check continuousMultilinearCurryRightEquiv' ℝ j E F

-- The relationship between iterated derivatives
#check iteratedFDeriv_succ_eq_comp_right

-- We expect: iteratedFDeriv ℝ j (fun y => fderiv ℝ f y) x =
--   (continuousMultilinearCurryRightEquiv' ℝ j E F) (iteratedFDeriv ℝ (j+1) f x)

theorem iteratedFDeriv_fderiv_eq_curryRight :
    iteratedFDeriv ℝ j (fun y => fderiv ℝ f y) x =
      (continuousMultilinearCurryRightEquiv' ℝ j E F) (iteratedFDeriv ℝ (j+1) f x) := by
  -- start from iteratedFDeriv_succ_eq_comp_right
  have h := (iteratedFDeriv_succ_eq_comp_right (𝕜 := ℝ) (f := f) (x := x) (n := j))
  -- h : iteratedFDeriv ℝ (j+1) f x = ((curryRightEquiv').symm ∘ iteratedFDeriv ℝ j (fun y => fderiv ℝ f y)) x
  -- rewrite and apply curryRightEquiv' to both sides
  --
  -- We'll massage h into the desired form.
  --
  -- unfold Function.comp at h
  --
  --
  --
  simpa [Function.comp] using congrArg (continuousMultilinearCurryRightEquiv' ℝ j E F) h

end ScratchIteratedFDerivRel
