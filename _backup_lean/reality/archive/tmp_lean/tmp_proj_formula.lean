import Mathlib.Analysis.InnerProductSpace.Projection.Basic

open scoped BigOperators
open scoped InnerProductSpace

example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v w : E) (hv : ‖v‖ = (1:ℝ)) :
    (ℂ ∙ v).starProjection w = ⟪v, w⟫_ℂ • v := by
  simpa using (Submodule.starProjection_unit_singleton (𝕜 := ℂ) (v := v) hv w)
