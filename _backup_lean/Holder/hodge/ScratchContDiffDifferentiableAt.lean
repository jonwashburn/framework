import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn

open scoped Distributions

namespace ScratchContDiffDifferentiableAt

open Classical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {K : Compacts E}

variable (f : 𝓓_{K}(E, F)) (x : E)

#check f.contDiff
#check (f.contDiff.differentiableAt : DifferentiableAt ℝ (fun y => (f : E → F) y) x)

end ScratchContDiffDifferentiableAt
