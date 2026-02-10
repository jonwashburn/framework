import Mathlib

open scoped BigOperators

-- Cauchy-Schwarz specialized: if ‖u‖^2 = 1, then ‖⟪u,v⟫‖ ≤ √(‖v‖^2)
-- We'll do it in EuclideanSpace to avoid custom norm.

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic

open WithLp

noncomputable def toE (v : Fin 8 → ℂ) : EuclideanSpace ℂ (Fin 8) := WithLp.toLp 2 v
noncomputable def normSq8 (v : Fin 8 → ℂ) : ℝ := ∑ i : Fin 8, Complex.normSq (v i)
noncomputable def innerProduct8 (u v : Fin 8 → ℂ) : ℂ := ∑ i : Fin 8, star (u i) * v i

lemma inner_toE (u v : Fin 8 → ℂ) : inner ℂ (toE u) (toE v) = innerProduct8 u v := by
  simp [toE, innerProduct8, PiLp.inner_apply, mul_comm]

lemma norm_toE (v : Fin 8 → ℂ) : ‖(toE v)‖ ^ 2 = normSq8 v := by
  simp [toE, normSq8, PiLp.norm_sq_eq_of_L2, Complex.normSq_eq_norm_sq]

lemma cs_unit (u v : Fin 8 → ℂ) (hu : normSq8 u = 1) :
    ‖innerProduct8 u v‖ ≤ Real.sqrt (normSq8 v) := by
  have hcs := norm_inner_le_norm (𝕜 := ℂ) (x := toE u) (y := toE v)
  -- rewrite
  have hu' : ‖toE u‖ = 1 := by
    have : ‖toE u‖ ^ 2 = (1:ℝ) := by simpa [norm_toE, hu]
    have hn : 0 ≤ ‖toE u‖ := norm_nonneg _
    calc
      ‖toE u‖ = Real.sqrt (‖toE u‖ ^ 2) := by
        symm
        simpa using (Real.sqrt_sq hn)
      _ = Real.sqrt 1 := by simpa [this]
      _ = (1:ℝ) := by norm_num
  -- also rewrite ‖toE v‖ = √(normSq8 v)
  have hv' : ‖toE v‖ = Real.sqrt (normSq8 v) := by
    have : ‖toE v‖ ^ 2 = normSq8 v := norm_toE v
    have hn : 0 ≤ ‖toE v‖ := norm_nonneg _
    calc
      ‖toE v‖ = Real.sqrt (‖toE v‖ ^ 2) := by
        symm
        simpa using (Real.sqrt_sq hn)
      _ = Real.sqrt (normSq8 v) := by simpa [this]
  --
  -- apply
  have : ‖innerProduct8 u v‖ ≤ ‖toE u‖ * ‖toE v‖ := by
    simpa [inner_toE] using hcs
  -- simplify
  simpa [hu', hv', one_mul] using this
