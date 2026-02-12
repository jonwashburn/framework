import Mathlib.Analysis.Normed.Module.Multilinear.Curry

namespace ScratchCurryFin1CLM

open Classical

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def curryFin1CLM :
    (E [×1]→L[ℝ] F) →L[ℝ] (E →L[ℝ] F) :=
  ((continuousMultilinearCurryFin1 ℝ E F).toContinuousLinearEquiv :
      (E [×1]→L[ℝ] F) ≃L[ℝ] (E →L[ℝ] F))

#check curryFin1CLM (E := E) (F := F)

end ScratchCurryFin1CLM
