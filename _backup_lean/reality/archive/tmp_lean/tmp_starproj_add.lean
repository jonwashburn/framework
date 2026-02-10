import Mathlib.Analysis.InnerProductSpace.Projection.Basic

open scoped BigOperators
open scoped InnerProductSpace

example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (b δ : E) :
    let S : Submodule ℂ E := ℂ ∙ b
    haveI : (Sᗮ).HasOrthogonalProjection := by infer_instance
    (Sᗮ).starProjection (b + δ) = (Sᗮ).starProjection δ := by
  classical
  intro S
  -- linearity
  have hlin : (Sᗮ).starProjection (b + δ) = (Sᗮ).starProjection b + (Sᗮ).starProjection δ := by
    simpa using (map_add (Sᗮ).starProjection b δ)
  -- show starProjection b = 0
  have hb0 : (Sᗮ).starProjection b = 0 := by
    have hbmem : b ∈ S := by
      simpa [S] using (Submodule.mem_span_singleton_self b)
    have : b ∈ (Sᗮ)ᗮ := (Submodule.le_orthogonal_orthogonal (K := S)) hbmem
    exact (Submodule.starProjection_apply_eq_zero_iff (K := Sᗮ)).2 this
  -- finish
  simpa [hlin, hb0]
