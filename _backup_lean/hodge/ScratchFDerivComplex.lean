import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Distribution.TestFunction

open scoped Distributions

namespace ScratchFDerivComplex

open Classical TopologicalSpace

variable {n : ℕ}

abbrev E := EuclideanSpace ℂ (Fin n)

-- For a function f : E → FiberAlt n k (complex normed spaces), can we take fderiv over ℂ?
variable {k : ℕ}
variable (f : E → FiberAlt n k)
variable (x : E)

#check fderiv ℂ f x
#check iteratedFDeriv ℂ 1 f x

end ScratchFDerivComplex
