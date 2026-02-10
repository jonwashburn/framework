import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

namespace ScratchIteratedFDerivRel2

open Classical

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable (f : E → F) (x : E) (j : ℕ)

theorem iteratedFDeriv_fderiv_eq_curryRight :
    iteratedFDeriv ℝ j (fun y => fderiv ℝ f y) x =
      (continuousMultilinearCurryRightEquiv' ℝ j E F) (iteratedFDeriv ℝ (j+1) f x) := by
  have h := (iteratedFDeriv_succ_eq_comp_right (𝕜 := ℝ) (f := f) (x := x) (n := j))
  -- apply curryRightEquiv' to both sides
  have h' := congrArg (continuousMultilinearCurryRightEquiv' ℝ j E F) h
  -- now simplify
  simpa [Function.comp] using h'.symm

end ScratchIteratedFDerivRel2
