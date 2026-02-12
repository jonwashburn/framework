import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

namespace ScratchFDerivIterated1

open Classical

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable (f : E → F) (x : E)

#check iteratedFDeriv_one_apply
#check fderiv

-- show relationship via curryFin1
example : (continuousMultilinearCurryFin1 ℝ E F) (iteratedFDeriv ℝ 1 f x) = fderiv ℝ f x := by
  -- ext v
  ext v
  -- compare evaluations
  -- for v : E, in the 1-multilinear map we feed snoc 0 v
  -- There is simp lemma continuousMultilinearCurryFin1_apply.
  simp [iteratedFDeriv_one_apply]

end ScratchFDerivIterated1
