import Mathlib

namespace Scratch

open scoped Real
open Complex

noncomputable section

-- Reuse the finite-interval integral lemma from earlier.

theorem integral_exp_smul_neg (a : ℂ) (ha : a ≠ 0) (B : ℝ) :
    ∫ t in (0:ℝ)..B, Complex.exp (t • (-a))
      = (Complex.exp (B • (-a)) - 1) * (-a)⁻¹ := by
  -- (copy from compiled prototype)
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) B,
      HasDerivAt (fun t : ℝ => Complex.exp (t • (-a)) * (-a)⁻¹)
        (Complex.exp (x • (-a))) x := by
    intro x hx
    have h_id : HasDerivAt (fun t : ℝ => t) (1:ℝ) x := by
      simpa using (hasDerivAt_id x)
    have h_inner : HasDerivAt (fun t : ℝ => t • (-a)) ((1:ℝ) • (-a)) x :=
      (HasDerivAt.smul_const (𝕜 := ℝ) (𝕜' := ℝ) (F := ℂ) (x := x) h_id (-a))
    have h_inner' : HasDerivAt (fun t : ℝ => t • (-a)) (-a) x := by
      simpa using h_inner
    have h_exp : HasDerivAt (fun t : ℝ => Complex.exp (t • (-a)))
        (Complex.exp (x • (-a)) * (-a)) x := by
      simpa [Function.comp] using ((Complex.hasDerivAt_exp (x • (-a))).comp x h_inner')
    have hmul : HasDerivAt (fun t : ℝ => (fun t => Complex.exp (t • (-a))) t * (-a)⁻¹)
        ((Complex.exp (x • (-a)) * (-a)) * (-a)⁻¹) x :=
      (HasDerivAt.mul_const (𝕜 := ℝ) (𝔸 := ℂ) (x := x) h_exp ((-a)⁻¹))
    simpa [ha] using hmul
  have hcont : Continuous (fun t : ℝ => Complex.exp (t • (-a))) := by
    fun_prop
  have hint : IntervalIntegrable (fun t : ℝ => Complex.exp (t • (-a))) MeasureTheory.volume (0:ℝ) B :=
    hcont.intervalIntegrable 0 B
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0:ℝ)) (b := B)
    (f := fun t : ℝ => Complex.exp (t • (-a)) * (-a)⁻¹)
    (f' := fun t : ℝ => Complex.exp (t • (-a)))
    hderiv hint
  calc
    ∫ t in (0:ℝ)..B, Complex.exp (t • (-a))
        = Complex.exp (B • (-a)) * (-a)⁻¹ - Complex.exp ((0:ℝ) • (-a)) * (-a)⁻¹ := by
            simpa using hFTC
    _ = Complex.exp (B • (-a)) * (-a)⁻¹ - (1:ℂ) * (-a)⁻¹ := by simp
    _ = (Complex.exp (B • (-a)) - 1) * (-a)⁻¹ := by ring

lemma norm_exp_neg_mul_ofReal (a : ℂ) (B : ℝ) :
    ‖Complex.exp (-( (B : ℂ) * a))‖ = Real.exp (-(B * a.re)) := by
  have hre : (-( (B : ℂ) * a)).re = -(B * a.re) := by
    simp [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_comm, mul_left_comm, mul_assoc]
  simpa [Complex.norm_exp, hre]

theorem tendsto_exp_neg_mul_ofReal_atTop (a : ℂ) (ha : 0 < a.re) :
    Filter.Tendsto (fun B : ℝ => Complex.exp (-( (B : ℂ) * a))) Filter.atTop (nhds (0:ℂ)) := by
  refine (tendsto_zero_iff_norm_tendsto_zero).2 ?_
  have hmul : Filter.Tendsto (fun B : ℝ => B * a.re) Filter.atTop Filter.atTop := by
    simpa using ((Filter.tendsto_id).atTop_mul_const ha)
  have hneg : Filter.Tendsto (fun B : ℝ => -(B * a.re)) Filter.atTop Filter.atBot :=
    (Filter.tendsto_neg_atTop_atBot.comp hmul)
  have hexp : Filter.Tendsto (fun B : ℝ => Real.exp (-(B * a.re))) Filter.atTop (nhds 0) :=
    (Real.tendsto_exp_atBot.comp hneg)
  have : (fun B : ℝ => ‖Complex.exp (-( (B : ℂ) * a))‖) = fun B : ℝ => Real.exp (-(B * a.re)) := by
    funext B
    simpa using (norm_exp_neg_mul_ofReal a B)
  simpa [this] using hexp

-- Main: the truncated integral tends to 1/a

theorem tendsto_integral_exp_smul_neg_atTop (a : ℂ) (ha0 : a ≠ 0) (ha : 0 < a.re) :
    Filter.Tendsto (fun B : ℝ => ∫ t in (0:ℝ)..B, Complex.exp (t • (-a)))
      Filter.atTop (nhds (a⁻¹)) := by
  -- rewrite the integral using the closed form, then take limit
  have hclosed : (fun B : ℝ => ∫ t in (0:ℝ)..B, Complex.exp (t • (-a)))
      = fun B : ℝ => (Complex.exp (B • (-a)) - 1) * (-a)⁻¹ := by
    funext B
    simpa using (integral_exp_smul_neg a ha0 B)

  -- exp(B•(-a)) → 0
  have hexp0 : Filter.Tendsto (fun B : ℝ => Complex.exp (B • (-a))) Filter.atTop (nhds (0:ℂ)) := by
    -- convert B•(-a) to -(↑B*a)
    have : (fun B : ℝ => Complex.exp (B • (-a))) = fun B : ℝ => Complex.exp (-( (B : ℂ) * a)) := by
      funext B
      -- B•(-a) = (↑B)*(-a) = -(↑B*a)
      simp [Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm]
    -- use the helper lemma on a
    simpa [this] using (tendsto_exp_neg_mul_ofReal_atTop a ha)

  have hlim : Filter.Tendsto (fun B : ℝ => (Complex.exp (B • (-a)) - 1) * (-a)⁻¹)
      Filter.atTop (nhds (((0:ℂ) - 1) * (-a)⁻¹)) := by
    have hsub : Filter.Tendsto (fun B : ℝ => Complex.exp (B • (-a)) - 1) Filter.atTop (nhds ((0:ℂ) - 1)) :=
      hexp0.sub tendsto_const_nhds
    have hconst : Filter.Tendsto (fun _B : ℝ => (-a)⁻¹) Filter.atTop (nhds ((-a)⁻¹)) := by
      simpa using
        (tendsto_const_nhds : Filter.Tendsto (fun _B : ℝ => (-a)⁻¹) Filter.atTop (nhds ((-a)⁻¹)))
    simpa using (hsub.mul hconst)

  -- simplify ((0:ℂ) - 1) * (-a)⁻¹ = a⁻¹
  have hsimp : ((0:ℂ) - 1) * (-a)⁻¹ = a⁻¹ := by
    -- (0-1) = -1 and (-a)⁻¹ = -a⁻¹
    simp [ha0]

  -- finish: move from the closed-form RHS back to the integral via `hclosed`
  -- Convert the integrand-side closed form to the simplified `simp` normal form.
  have hclosed_simp :
      (fun B : ℝ => ∫ t in (0:ℝ)..B, Complex.exp (t • (-a)))
        = fun B : ℝ => -((Complex.exp (-( (B : ℂ) * a)) - 1) * a⁻¹) := by
    funext B
    -- start from the earlier closed form, then simp to normal form
    have h := congrArg (fun x => x) (integral_exp_smul_neg a ha0 B)
    -- `simp` rewrites `B • (-a)` and `(-a)⁻¹`
    simpa [Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm] using h

  have hlim_simp :
      Filter.Tendsto (fun B : ℝ => -((Complex.exp (-( (B : ℂ) * a)) - 1) * a⁻¹))
        Filter.atTop (nhds (a⁻¹)) := by
    -- hlim already tends to nhds (((0)-1)*(-a)⁻¹); simp transforms both sides.
    simpa [hsimp, Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm] using hlim

  -- finish
  simpa [hclosed_simp] using hlim_simp

end

end Scratch
