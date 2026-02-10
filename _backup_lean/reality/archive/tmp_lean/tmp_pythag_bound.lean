import Mathlib.Analysis.InnerProductSpace.Projection.Basic

open scoped BigOperators
open scoped InnerProductSpace

namespace Test

example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (b δ : E) (hb : ‖b‖ = (1:ℝ)) :
    let S : Submodule ℂ E := ℂ ∙ b
    haveI : S.HasOrthogonalProjection := by infer_instance
    ‖b + δ‖ ^ 2 ≤ ‖(inner ℂ b (b + δ)) • b‖ ^ 2 + ‖δ‖ ^ 2 := by
  classical
  intro S
  -- Use Pythagorean theorem with S
  have hpy : ‖b + δ‖ ^ 2 = ‖S.starProjection (b + δ)‖ ^ 2 + ‖Sᗮ.starProjection (b + δ)‖ ^ 2 :=
    Submodule.norm_sq_eq_add_norm_sq_starProjection (x := b + δ) (S := S)
  -- Bound orthogonal part by ‖δ‖
  have horth_eq : Sᗮ.starProjection (b + δ) = Sᗮ.starProjection δ := by
    have hlin : Sᗮ.starProjection (b + δ) = Sᗮ.starProjection b + Sᗮ.starProjection δ := by
      simpa using (map_add (Sᗮ).starProjection b δ)
    have hb0 : Sᗮ.starProjection b = 0 := by
      have hbmem : b ∈ S := by
        simpa [S] using (Submodule.mem_span_singleton_self b)
      have : b ∈ (Sᗮ)ᗮ := (Submodule.le_orthogonal_orthogonal (K := S)) hbmem
      exact (Submodule.starProjection_apply_eq_zero_iff (K := Sᗮ)).2 this
    simpa [hlin, hb0]
  have horth_le : ‖Sᗮ.starProjection (b + δ)‖ ≤ ‖δ‖ := by
    simpa [horth_eq] using (Submodule.norm_starProjection_apply_le (K := Sᗮ) δ)
  have horth_sq : ‖Sᗮ.starProjection (b + δ)‖ ^ 2 ≤ ‖δ‖ ^ 2 := by
    have hn : 0 ≤ ‖Sᗮ.starProjection (b + δ)‖ := norm_nonneg _
    have := mul_self_le_mul_self hn horth_le
    simpa [pow_two] using this
  -- rewrite S.starProjection for unit b
  have hproj : S.starProjection (b + δ) = (inner ℂ b (b + δ)) • b := by
    simpa [S] using (Submodule.starProjection_unit_singleton (𝕜 := ℂ) (v := b) hb (b + δ))
  -- combine
  calc
    ‖b + δ‖ ^ 2 = ‖S.starProjection (b + δ)‖ ^ 2 + ‖Sᗮ.starProjection (b + δ)‖ ^ 2 := hpy
    _ ≤ ‖S.starProjection (b + δ)‖ ^ 2 + ‖δ‖ ^ 2 := by gcongr
    _ = ‖(inner ℂ b (b + δ)) • b‖ ^ 2 + ‖δ‖ ^ 2 := by simpa [hproj]

end Test
