import Mathlib.Analysis.InnerProductSpace.Projection.Basic

-- Try using lemma without opening InnerProductSpace scope.
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (v w : E) (hv : ‖v‖ = (1:ℝ)) :
    (ℂ ∙ v).starProjection w = inner ℂ v w • v := by
  -- rewrite ⟪v,w⟫_ℂ as `inner ℂ v w`
  simpa using (Submodule.starProjection_unit_singleton (𝕜 := ℂ) (v := v) hv w)
