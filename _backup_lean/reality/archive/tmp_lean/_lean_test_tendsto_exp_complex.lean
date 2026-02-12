import Mathlib

namespace Scratch

open scoped Real
open Complex

noncomputable section

-- Helper: rewrite norm(exp(-(↑B * a))) into exp(-(B * a.re)).
lemma norm_exp_neg_mul_ofReal (a : ℂ) (B : ℝ) :
    ‖Complex.exp (-( (B : ℂ) * a))‖ = Real.exp (-(B * a.re)) := by
  -- Use norm_exp and compute the real part.
  have hre : (-( (B : ℂ) * a)).re = -(B * a.re) := by
    -- Expand re of mul and ofReal
    simp [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_assoc, mul_left_comm, mul_comm]
  simpa [Complex.norm_exp, hre]

theorem tendsto_exp_neg_mul_ofReal_atTop (a : ℂ) (ha : 0 < a.re) :
    Filter.Tendsto (fun B : ℝ => Complex.exp (-( (B : ℂ) * a))) Filter.atTop (nhds (0:ℂ)) := by
  -- Reduce to norm → 0.
  refine (tendsto_zero_iff_norm_tendsto_zero).2 ?_

  have hmul : Filter.Tendsto (fun B : ℝ => B * a.re) Filter.atTop Filter.atTop := by
    simpa using ((Filter.tendsto_id).atTop_mul_const ha)
  have hneg : Filter.Tendsto (fun B : ℝ => -(B * a.re)) Filter.atTop Filter.atBot :=
    (Filter.tendsto_neg_atTop_atBot.comp hmul)
  have hexp : Filter.Tendsto (fun B : ℝ => Real.exp (-(B * a.re))) Filter.atTop (nhds 0) :=
    (Real.tendsto_exp_atBot.comp hneg)

  -- Rewrite the norm using the helper lemma.
  have : (fun B : ℝ => ‖Complex.exp (-( (B : ℂ) * a))‖) = fun B : ℝ => Real.exp (-(B * a.re)) := by
    funext B
    simpa using (norm_exp_neg_mul_ofReal a B)

  simpa [this] using hexp

end

end Scratch
