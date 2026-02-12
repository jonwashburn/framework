import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

open scoped Distributions

namespace ScratchDerivTestFunctionCurry

open Classical TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Ω : TopologicalSpace.Opens E}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

-- Target type: continuous linear maps E →L[ℝ] F
abbrev DerivTarget := E →L[ℝ] F

-- Show we can map a test function valued in multilinear maps (Fin 1) to linear maps using postcompCLM
#check continuousMultilinearCurryFin1
#check TestFunction.postcompCLM

-- The curry equivalence gives a linear isometry equiv between E[×1]→L F and E→L F
#check (continuousMultilinearCurryFin1 ℝ E F)

-- Its underlying continuous linear map
#check (continuousMultilinearCurryFin1 ℝ E F).toContinuousLinearMap

end ScratchDerivTestFunctionCurry
