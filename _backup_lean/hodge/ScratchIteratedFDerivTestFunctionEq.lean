import Mathlib.Analysis.Distribution.TestFunction

open scoped Distributions

namespace ScratchIteratedFDerivTestFunctionEq

open Classical TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Ω : TopologicalSpace.Opens E}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {K : Compacts E} (K_sub_Ω : (K : Set E) ⊆ (Ω : Set E))

-- We'll test if iterated derivative of the ofSupportedIn map agrees with ofSupportedIn of iterated derivative.
-- This is a proposition, not necessarily definitional.

open ContDiffMapSupportedIn

-- Setup
variable (f : 𝓓_{K}(E, F))

-- `iteratedFDeriv` in the K-space
#check (ContDiffMapSupportedIn.iteratedFDerivLM (𝕜 := ℝ) (E := E) (F := F) (K := K) 1) f

-- `iteratedFDerivTestFunction` on the LF space is not in Mathlib; we'd need our local version.

end ScratchIteratedFDerivTestFunctionEq
