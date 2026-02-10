import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic

open scoped BigOperators
open scoped InnerProductSpace

namespace Test

open WithLp

noncomputable def toEuclidean8 (v : Fin 8 → ℂ) : EuclideanSpace ℂ (Fin 8) :=
  WithLp.toLp 2 v

noncomputable def normSq8 (v : Fin 8 → ℂ) : ℝ :=
  Finset.univ.sum (fun i => Complex.normSq (v i))

noncomputable def innerProduct8 (u v : Fin 8 → ℂ) : ℂ :=
  Finset.univ.sum (fun i => star (u i) * v i)

lemma inner_toEuclidean8 (u v : Fin 8 → ℂ) :
    inner ℂ (toEuclidean8 u) (toEuclidean8 v) = innerProduct8 u v := by
  simp [toEuclidean8, innerProduct8, PiLp.inner_apply, mul_comm]

lemma norm_toEuclidean8_sq (v : Fin 8 → ℂ) :
    ‖(toEuclidean8 v)‖ ^ 2 = normSq8 v := by
  simp [toEuclidean8, normSq8, PiLp.norm_sq_eq_of_L2, Complex.normSq_eq_norm_sq]

-- A bound: ‖u+δ‖^2 ≤ ‖(⟪u,u+δ⟫)•u‖^2 + ‖δ‖^2 when ‖u‖=1.
lemma normSq8_add_le (u δ : Fin 8 → ℂ) (hu : normSq8 u = 1) :
    normSq8 (fun i => u i + δ i) ≤
      Complex.normSq (innerProduct8 u (fun i => u i + δ i)) + normSq8 δ := by
  -- Work in EuclideanSpace
  let b : EuclideanSpace ℂ (Fin 8) := toEuclidean8 u
  let d : EuclideanSpace ℂ (Fin 8) := toEuclidean8 δ
  have hb_norm : ‖b‖ = (1:ℝ) := by
    -- ‖b‖^2 = normSq8 u = 1
    have hsq : ‖b‖ ^ 2 = (1:ℝ) := by simpa [b, norm_toEuclidean8_sq, hu]
    have hn : 0 ≤ ‖b‖ := norm_nonneg _
    -- √(‖b‖^2) = ‖b‖
    have : ‖b‖ = Real.sqrt (‖b‖ ^ 2) := by
      symm
      simpa using (Real.sqrt_sq hn)
    --
    -- simplify
    --
    -- √1 = 1
    --
    --
    calc
      ‖b‖ = Real.sqrt (‖b‖ ^ 2) := this
      _ = Real.sqrt 1 := by simpa [hsq]
      _ = (1:ℝ) := by norm_num
  -- apply pythag bound from earlier
  have hineq : ‖b + d‖ ^ 2 ≤ ‖(inner ℂ b (b + d)) • b‖ ^ 2 + ‖d‖ ^ 2 := by
    -- use our earlier lemma pattern
    --
    --
    simpa using (by
      -- inline the lemma from tmp_pythag_bound
      --
      --
      exact (by
        -- instantiate S
        let S : Submodule ℂ (EuclideanSpace ℂ (Fin 8)) := ℂ ∙ b
        haveI : S.HasOrthogonalProjection := by infer_instance
        -- reuse the proof from tmp_pythag_bound
        have hpy : ‖b + d‖ ^ 2 = ‖S.starProjection (b + d)‖ ^ 2 + ‖Sᗮ.starProjection (b + d)‖ ^ 2 :=
          Submodule.norm_sq_eq_add_norm_sq_starProjection (x := b + d) (S := S)
        have horth_eq : Sᗮ.starProjection (b + d) = Sᗮ.starProjection d := by
          have hlin : Sᗮ.starProjection (b + d) = Sᗮ.starProjection b + Sᗮ.starProjection d := by
            simpa using (map_add (Sᗮ).starProjection b d)
          have hb0 : Sᗮ.starProjection b = 0 := by
            have hbmem : b ∈ S := by
              simpa [S] using (Submodule.mem_span_singleton_self b)
            have : b ∈ (Sᗮ)ᗮ := (Submodule.le_orthogonal_orthogonal (K := S)) hbmem
            exact (Submodule.starProjection_apply_eq_zero_iff (K := Sᗮ)).2 this
          simpa [hlin, hb0]
        have horth_le : ‖Sᗮ.starProjection (b + d)‖ ≤ ‖d‖ := by
          simpa [horth_eq] using (Submodule.norm_starProjection_apply_le (K := Sᗮ) d)
        have horth_sq : ‖Sᗮ.starProjection (b + d)‖ ^ 2 ≤ ‖d‖ ^ 2 := by
          have hn : 0 ≤ ‖Sᗮ.starProjection (b + d)‖ := norm_nonneg _
          have := mul_self_le_mul_self hn horth_le
          simpa [pow_two] using this
        have hproj : S.starProjection (b + d) = (inner ℂ b (b + d)) • b := by
          simpa [S] using (Submodule.starProjection_unit_singleton (𝕜 := ℂ) (v := b) hb_norm (b + d))
        -- combine
        calc
          ‖b + d‖ ^ 2 = ‖S.starProjection (b + d)‖ ^ 2 + ‖Sᗮ.starProjection (b + d)‖ ^ 2 := hpy
          _ ≤ ‖S.starProjection (b + d)‖ ^ 2 + ‖d‖ ^ 2 := by gcongr
          _ = ‖(inner ℂ b (b + d)) • b‖ ^ 2 + ‖d‖ ^ 2 := by simpa [hproj]))
  -- translate back to normSq8
  have hb_add : toEuclidean8 (fun i => u i + δ i) = b + d := by
    ext i
    simp [toEuclidean8, b, d]
  -- Now: ‖b+d‖^2 = normSq8(u+δ), and ‖d‖^2 = normSq8 δ.
  -- Also, ‖(inner b (b+d))•b‖^2 = ‖inner b (b+d)‖^2 (since ‖b‖=1) = normSq(innerProduct8 u (u+δ)).
  -- TODO: finish rewriting.
  sorry

end Test
