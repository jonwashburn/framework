import Hodge.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Distribution.TestFunction

open scoped Distributions

namespace ScratchTestFunctionContDiffC

open Classical TopologicalSpace

variable {n : ℕ}

abbrev E := EuclideanSpace ℂ (Fin n)

variable {Ω : TopologicalSpace.Opens E}

variable (f : 𝓓(Ω, ℂ))

#check f.contDiff
-- Try to view contDiff over ℂ
#check (show ContDiff ℂ (⊤ : WithTop ℕ∞) (f : E → ℂ) from by
  -- should fail?
  simpa using (f.contDiff))

end ScratchTestFunctionContDiffC
