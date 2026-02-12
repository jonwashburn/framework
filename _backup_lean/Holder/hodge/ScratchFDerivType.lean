import Hodge.Basic
import Mathlib.Analysis.Distribution.TestFunction

open scoped Distributions

namespace ScratchFDerivType

open Classical TopologicalSpace

abbrev Euclid (n : ℕ) := EuclideanSpace ℂ (Fin n)

abbrev FiberAltR (n : ℕ) (k : ℕ) := (TangentModel n) [⋀^Fin k]→L[ℝ] ℂ

variable {n k : ℕ}
variable {Ω : TopologicalSpace.Opens (Euclid n)}

variable (f : 𝓓(Ω, FiberAltR n k))

#check iteratedFDeriv ℝ 1 (f : Euclid n → FiberAltR n k)
#check (fderiv ℝ (f : Euclid n → FiberAltR n k))

end ScratchFDerivType
