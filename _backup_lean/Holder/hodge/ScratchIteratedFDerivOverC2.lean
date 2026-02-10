import Hodge.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Distribution.TestFunction

open scoped Distributions

namespace ScratchIteratedFDerivOverC2

open Classical TopologicalSpace

variable {n : ℕ}

abbrev E := EuclideanSpace ℂ (Fin n)

variable {Ω : TopologicalSpace.Opens E}

variable (f : 𝓓(Ω, ℂ))

#check iteratedFDeriv ℂ 1 (f : E → ℂ)
#check iteratedFDeriv ℝ 1 (f : E → ℂ)

end ScratchIteratedFDerivOverC2
