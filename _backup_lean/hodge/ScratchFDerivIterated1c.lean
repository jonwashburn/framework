import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

namespace ScratchFDerivIterated1c

open Classical

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable (f : E → F) (x : E)

example : (continuousMultilinearCurryFin1 ℝ E F) (iteratedFDeriv ℝ 1 f x) = fderiv ℝ f x := by
  ext v
  -- reduce to evaluation at the last index
  have h0 : (0 : Fin 1) = Fin.last 0 := by
    ext; rfl
  -- now simp
  simpa [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply, h0]

end ScratchFDerivIterated1c
