import Mathlib.Analysis.InnerProductSpace.Projection.Basic

open scoped InnerProductSpace

example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (b d : E) (hb : ‖b‖ = (1:ℝ)) :
    ((ℂ ∙ b).starProjection (b + d)) = (ℂ ∙ b).starProjection b + (ℂ ∙ b).starProjection d := by
  -- does simp do this?
  simpa using (map_add ((ℂ ∙ b).starProjection) b d)
