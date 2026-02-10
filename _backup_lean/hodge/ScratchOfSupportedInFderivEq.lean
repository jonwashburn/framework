import Mathlib.Analysis.Distribution.TestFunction

open scoped Distributions

namespace ScratchOfSupportedInFderivEq

open Classical TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Ω : TopologicalSpace.Opens E}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {K : Compacts E} (K_sub_Ω : (K : Set E) ⊆ (Ω : Set E))

#check TestFunction.ofSupportedIn
#check TestFunction.ofSupportedInCLM

-- Compare fderiv of ofSupportedIn and ofSupportedIn of fderiv (pointwise)
example (f : 𝓓_{K}(E, F)) (x : E) :
    fderiv ℝ (TestFunction.ofSupportedIn (n := (⊤ : ℕ∞)) (Ω := Ω) (F := F) K_sub_Ω f : E → F) x =
      fderiv ℝ (f : E → F) x := by
  rfl

end ScratchOfSupportedInFderivEq
