import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Distribution.TestFunction

open scoped Distributions

namespace ScratchIteratedFDerivOverC

open Classical TopologicalSpace

variable {n : ℕ}

abbrev E := EuclideanSpace ℂ (Fin n)

variable {Ω : TopologicalSpace.Opens E}

-- test functions into ℂ
variable (f : 𝓓(Ω, ℂ))

-- Can we take iteratedFDeriv over ℂ of the underlying function?
#check iteratedFDeriv ℂ 1 (f : E → ℂ)
#check iteratedFDeriv ℝ 1 (f : E → ℂ)

end ScratchIteratedFDerivOverC
