import Hodge.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Distribution.TestFunction

namespace ScratchFDerivComplex2

open Classical

variable {n k : ℕ}

abbrev E := EuclideanSpace ℂ (Fin n)

variable (f : E → FiberAlt n k)
variable (x : E)

#check fderiv ℂ f x
#check iteratedFDeriv ℂ 1 f x

end ScratchFDerivComplex2
