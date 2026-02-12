import Mathlib.Analysis.InnerProductSpace.Projection.Basic

open scoped BigOperators

open scoped InnerProductSpace

example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (b : E) :
    let S : Submodule ℂ E := ℂ ∙ b
    haveI : (Sᗮ).HasOrthogonalProjection := by infer_instance
    (Sᗮ).starProjection b = 0 := by
  classical
  intro S
  -- use starProjection_apply_eq_zero_iff: K.starProjection v = 0 ↔ v ∈ Kᗮ
  have : b ∈ (Sᗮ)ᗮ := by
    -- b ∈ S, and S ≤ Sᗮᗮ
    have hbS : b ∈ S := by
      simpa [S] using (Submodule.mem_span_singleton_self b)
    -- use `Submodule.le_orthogonal_orthogonal`
    exact (Submodule.le_orthogonal_orthogonal (K := S)) hbS
  -- now apply iff
  exact (Submodule.starProjection_apply_eq_zero_iff (K := Sᗮ)).2 this
