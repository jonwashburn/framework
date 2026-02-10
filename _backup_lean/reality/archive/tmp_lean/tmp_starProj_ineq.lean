import Mathlib.Analysis.InnerProductSpace.Projection.Basic

open scoped BigOperators
open scoped InnerProductSpace

example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (b x δ : E) (hb : ‖b‖ = (1:ℝ)) :
    -- Let S be span{b}; show that orthogonal component of x=b+δ has norm ≤ ‖δ‖
    let S : Submodule ℂ E := ℂ ∙ b
    haveI : S.HasOrthogonalProjection := by infer_instance
    ‖Sᗮ.starProjection (b + δ)‖ ≤ ‖δ‖ := by
  classical
  intro S
  -- Use linearity and that projection of b lies in S (so orthogonal projection onto Sᗮ is 0)
  -- `Sᗮ.starProjection` is linear.
  --
  have hlin : Sᗮ.starProjection (b + δ) = Sᗮ.starProjection b + Sᗮ.starProjection δ := by
    simp [map_add]
  -- b ∈ S, so starProjection onto Sᗮ is 0.
  have hbmem : b ∈ S := by
    -- b in span
    simpa [S] using (Submodule.mem_span_singleton_self b)
  have hb0 : Sᗮ.starProjection b = 0 := by
    -- projection of element in S onto orthogonal complement is 0
    -- lemma: `orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero`? maybe.
    --
    sorry
  --
  -- then Sᗮ.starProjection (b+δ) = Sᗮ.starProjection δ
  -- and norm is ≤ ‖δ‖ because projection is nonexpansive.
  --
  sorry
