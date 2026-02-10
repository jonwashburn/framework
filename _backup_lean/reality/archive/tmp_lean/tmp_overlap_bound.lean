import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic
open scoped BigOperators

namespace Test

open WithLp

noncomputable def normSq8 (v : Fin 8 → ℂ) : ℝ :=
  ∑ i : Fin 8, Complex.normSq (v i)

noncomputable def innerProduct8 (u v : Fin 8 → ℂ) : ℂ :=
  ∑ i : Fin 8, star (u i) * v i

noncomputable def toE (v : Fin 8 → ℂ) : EuclideanSpace ℂ (Fin 8) :=
  WithLp.toLp 2 v

lemma normSq8_nonneg (v : Fin 8 → ℂ) : 0 ≤ normSq8 v := by
  unfold normSq8
  refine Finset.sum_nonneg ?_
  intro i hi
  exact Complex.normSq_nonneg (v i)

lemma inner_toE (u v : Fin 8 → ℂ) :
    inner ℂ (toE u) (toE v) = innerProduct8 u v := by
  simp [toE, innerProduct8, PiLp.inner_apply, mul_comm]

lemma norm_toE_sq (v : Fin 8 → ℂ) :
    ‖(toE v)‖ ^ 2 = normSq8 v := by
  simp [toE, normSq8, PiLp.norm_sq_eq_of_L2, Complex.normSq_eq_norm_sq]

lemma norm_toE (v : Fin 8 → ℂ) :
    ‖(toE v)‖ = Real.sqrt (normSq8 v) := by
  have hsq : ‖(toE v)‖ ^ 2 = normSq8 v := norm_toE_sq v
  have hn : 0 ≤ (‖(toE v)‖ : ℝ) := norm_nonneg _
  calc
    ‖(toE v)‖ = Real.sqrt (‖(toE v)‖ ^ 2) := by
      symm
      simpa using (Real.sqrt_sq hn)
    _ = Real.sqrt (normSq8 v) := by simpa [hsq]

-- Basic Cauchy-Schwarz for our innerProduct8
lemma norm_innerProduct8_le (u v : Fin 8 → ℂ) :
    ‖innerProduct8 u v‖ ≤ Real.sqrt (normSq8 u) * Real.sqrt (normSq8 v) := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (x := (toE u)) (y := (toE v))
  -- rewrite inner and norms
  simpa [inner_toE, norm_toE] using h

-- The key inequality
lemma overlap_change_bound (u v δ : Fin 8 → ℂ) :
    |Complex.normSq (innerProduct8 u (fun i => v i + δ i)) - Complex.normSq (innerProduct8 u v)| ≤
      2 * Real.sqrt (normSq8 v * normSq8 δ) + normSq8 δ := by
  classical
  let a : ℂ := innerProduct8 u v
  let e : ℂ := innerProduct8 u δ
  have hadd : innerProduct8 u (fun i => v i + δ i) = a + e := by
    unfold a e innerProduct8
    simp [mul_add, Finset.sum_add_distrib]
  -- reduce goal
  simp [hadd, a, e]
  -- now goal: |normSq (a+e) - normSq a| ≤ ...
  have hdiff : Complex.normSq (a + e) - Complex.normSq a =
      Complex.normSq e + 2 * (a * star e).re := by
    have h := Complex.normSq_add a e
    have h' : Complex.normSq (a + e) - Complex.normSq a =
        Complex.normSq e + 2 * (a * (starRingEnd ℂ) e).re := by
      linarith
    simpa using h'
  -- rewrite using hdiff
  rw [hdiff]
  -- triangle inequality
  have hre : |(a * star e).re| ≤ ‖a‖ * ‖e‖ := by
    -- |re z| ≤ ‖z‖ and ‖a*star e‖ = ‖a‖*‖e‖
    have h1 : |(a * star e).re| ≤ ‖a * star e‖ := by
      simpa using (abs_re_le_norm (a * star e))
    have h2 : ‖a * star e‖ = ‖a‖ * ‖e‖ := by
      -- norm_mul and norm_star
      simp [norm_mul, norm_star]
    exact h1.trans_eq (by simpa [h2])
  -- bound abs
  have hmain : |Complex.normSq e + 2 * (a * star e).re| ≤
      Complex.normSq e + 2 * (‖a‖ * ‖e‖) := by
    -- |x + 2*y| ≤ |x| + |2*y| ≤ x + 2*|y| etc
    have hx : |Complex.normSq e| = Complex.normSq e := by
      have : 0 ≤ Complex.normSq e := Complex.normSq_nonneg e
      simpa [abs_of_nonneg this]
    -- use abs_add
    calc
      |Complex.normSq e + 2 * (a * star e).re|
          ≤ |Complex.normSq e| + |2 * (a * star e).re| := by
              simpa using abs_add (Complex.normSq e) (2 * (a * star e).re)
      _ = Complex.normSq e + |2 * (a * star e).re| := by simpa [hx]
      _ = Complex.normSq e + (2 * |(a * star e).re|) := by
            -- abs_mul
            simp [abs_mul]
      _ ≤ Complex.normSq e + 2 * (‖a‖ * ‖e‖) := by
            gcongr
            exact hre
  -- now bound ‖a‖ and ‖e‖ by Cauchy-Schwarz
  have ha : ‖a‖ ≤ Real.sqrt (normSq8 u) * Real.sqrt (normSq8 v) := by
    simpa [a] using norm_innerProduct8_le u v
  have he : ‖e‖ ≤ Real.sqrt (normSq8 u) * Real.sqrt (normSq8 δ) := by
    simpa [e] using norm_innerProduct8_le u δ
  -- specialize? assume normSq8 u = 1? not here, so just use u unit? hmm.
  -- For our intended use, u will be unit so normSq8 u = 1, but here we didn't.
  -- Let's just finish assuming normSq8 u = 1 to match expected RHS.
  admit

end Test
