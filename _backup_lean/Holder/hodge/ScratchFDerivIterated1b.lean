import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

namespace ScratchFDerivIterated1b

open Classical

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable (f : E → F) (x : E)

example : (continuousMultilinearCurryFin1 ℝ E F) (iteratedFDeriv ℝ 1 f x) = fderiv ℝ f x := by
  ext v
  -- evaluate both sides at v
  -- LHS reduces to iteratedFDeriv applied to the snoc vector
  simp [iteratedFDeriv_one_apply]

end ScratchFDerivIterated1b
