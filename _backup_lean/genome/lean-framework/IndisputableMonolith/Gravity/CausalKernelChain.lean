import Mathlib
import IndisputableMonolith.Gravity.CaldeiraLeggett

/-!
# Causal-kernel chain: time-domain exponential kernel → transfer function → limits

This module formalizes the **single-timescale exponential** memory kernel
(Debye/single-pole response) and its frequency-domain properties.

Goal
----
Formalize, end-to-end:

- the time-domain exponential kernel (causal, \(t \ge 0\)),
- its frequency response / transfer function \(H(i\omega)\),
- the steady-state (ω→0) and Newtonian (ω→∞) limits for the response \(C(\omega)=\Re H(i\omega)\).

Scope / limitations
-------------------
This is the **Debye** (single-pole) realization only. The paper allows broader spectral
densities; those require additional Fourier/Laplace machinery and are not yet formalized.
-/

namespace IndisputableMonolith
namespace Gravity
namespace CausalKernelChain

open scoped Real
open Complex

noncomputable section

/-! ## Core analytic lemmas: ∫ exp(-a t) dt and exp(-a B) → 0 -/

/-- Finite-interval complex exponential integral:
\[
\int_0^B e^{-a t}\,dt = \frac{1 - e^{-aB}}{a}.
\]

We state it in the convenient `t • (-a)` form, where `t : ℝ` and `a : ℂ`. -/
theorem integral_exp_smul_neg (a : ℂ) (ha : a ≠ 0) (B : ℝ) :
    ∫ t in (0 : ℝ)..B, Complex.exp (t • (-a))
      = (Complex.exp (B • (-a)) - 1) * (-a)⁻¹ := by
  -- Antiderivative F(t) = exp(t•(-a)) * (-a)⁻¹
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) B,
      HasDerivAt (fun t : ℝ => Complex.exp (t • (-a)) * (-a)⁻¹)
        (Complex.exp (x • (-a))) x := by
    intro x hx
    have h_id : HasDerivAt (fun t : ℝ => t) (1 : ℝ) x := by
      simpa using (hasDerivAt_id x)
    have h_inner :
        HasDerivAt (fun t : ℝ => t • (-a)) ((1 : ℝ) • (-a)) x :=
      (HasDerivAt.smul_const (𝕜 := ℝ) (𝕜' := ℝ) (F := ℂ) (x := x) h_id (-a))
    have h_inner' : HasDerivAt (fun t : ℝ => t • (-a)) (-a) x := by
      simpa using h_inner
    have h_exp :
        HasDerivAt (fun t : ℝ => Complex.exp (t • (-a)))
          (Complex.exp (x • (-a)) * (-a)) x := by
      simpa [Function.comp] using ((Complex.hasDerivAt_exp (x • (-a))).comp x h_inner')
    have hmul :
        HasDerivAt (fun t : ℝ => (fun t => Complex.exp (t • (-a))) t * (-a)⁻¹)
          ((Complex.exp (x • (-a)) * (-a)) * (-a)⁻¹) x :=
      (HasDerivAt.mul_const (𝕜 := ℝ) (𝔸 := ℂ) (x := x) h_exp ((-a)⁻¹))
    -- cancel `(-a) * (-a)⁻¹` using `ha`
    simpa [ha] using hmul

  have hcont : Continuous (fun t : ℝ => Complex.exp (t • (-a))) := by
    fun_prop
  have hint :
      IntervalIntegrable (fun t : ℝ => Complex.exp (t • (-a)))
        MeasureTheory.volume (0 : ℝ) B :=
    hcont.intervalIntegrable 0 B

  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := B)
      (f := fun t : ℝ => Complex.exp (t • (-a)) * (-a)⁻¹)
      (f' := fun t : ℝ => Complex.exp (t • (-a)))
      hderiv hint

  -- Rewrite F(B) - F(0) into the desired algebraic form.
  calc
    ∫ t in (0 : ℝ)..B, Complex.exp (t • (-a))
        = Complex.exp (B • (-a)) * (-a)⁻¹ - Complex.exp ((0 : ℝ) • (-a)) * (-a)⁻¹ := by
            simpa using hFTC
    _ = Complex.exp (B • (-a)) * (-a)⁻¹ - (1 : ℂ) * (-a)⁻¹ := by simp
    _ = (Complex.exp (B • (-a)) - 1) * (-a)⁻¹ := by ring


/-- Helper: norm of `exp (-(↑B * a))` is `exp (-(B * Re a))`. -/
lemma norm_exp_neg_mul_ofReal (a : ℂ) (B : ℝ) :
    ‖Complex.exp (-( (B : ℂ) * a))‖ = Real.exp (-(B * a.re)) := by
  have hre : (-( (B : ℂ) * a)).re = -(B * a.re) := by
    simp [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_comm, mul_left_comm]
  simpa [Complex.norm_exp, hre]


/-- If `Re(a) > 0`, then `exp (-(↑B * a)) → 0` as `B → +∞`. -/
theorem tendsto_exp_neg_mul_ofReal_atTop (a : ℂ) (ha : 0 < a.re) :
    Filter.Tendsto (fun B : ℝ => Complex.exp (-( (B : ℂ) * a))) Filter.atTop (nhds (0 : ℂ)) := by
  -- Reduce to the norm tending to 0.
  refine (tendsto_zero_iff_norm_tendsto_zero).2 ?_

  have hmul : Filter.Tendsto (fun B : ℝ => B * a.re) Filter.atTop Filter.atTop := by
    simpa using ((Filter.tendsto_id).atTop_mul_const ha)
  have hneg : Filter.Tendsto (fun B : ℝ => -(B * a.re)) Filter.atTop Filter.atBot :=
    (Filter.tendsto_neg_atTop_atBot.comp hmul)
  have hexp : Filter.Tendsto (fun B : ℝ => Real.exp (-(B * a.re))) Filter.atTop (nhds 0) :=
    (Real.tendsto_exp_atBot.comp hneg)

  have hnorm_eq :
      (fun B : ℝ => ‖Complex.exp (-( (B : ℂ) * a))‖) = fun B : ℝ => Real.exp (-(B * a.re)) := by
    funext B
    simpa using (norm_exp_neg_mul_ofReal a B)

  simpa [hnorm_eq] using hexp


/-! ## Debye kernel → transfer function -/

/-- The (complex) transfer function for a single-pole (Debye) response:
\[
H(i\omega) = 1 + \frac{\Delta}{1 + i\omega\tau}.
\]
This matches the structure in `Gravity.CaldeiraLeggett.TransferFunction`, but is a complex-valued
frequency response rather than its extracted real part. -/
def transfer_function_complex (H : CaldeiraLeggett.TransferFunction) (ω : ℝ) : ℂ :=
  (1 : ℂ) + (H.Δ : ℂ) / ((1 : ℂ) + Complex.I * (ω : ℂ) * (H.τ : ℂ))


/-- The Debye exponential kernel for a single-timescale response:
\[
\Gamma(t) = \frac{\Delta}{\tau} e^{-t/\tau},\quad t \ge 0.
\]
We treat it as a function on `ℝ` and integrate it on `[0,B]` (then take `B → ∞`). -/
def debye_kernel (H : CaldeiraLeggett.TransferFunction) (t : ℝ) : ℝ :=
  (H.Δ / H.τ) * Real.exp (-t / H.τ)


/-- Truncated (finite-horizon) frequency response contribution from the Debye kernel:
\[
K_B(\omega)=\int_0^B \Gamma(t)\,e^{-i\omega t}\,dt.
\]
The full transfer function is `1 + K_∞(ω)`. -/
def kernel_response_trunc (H : CaldeiraLeggett.TransferFunction) (ω B : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..B,
    ((debye_kernel H t : ℝ) : ℂ) * Complex.exp (-(Complex.I * (ω : ℂ) * (t : ℂ)))


/-!
### Bridge lemma (frequency-domain closed form)

For τ>0, define `a = (1/τ) + i ω`. Then

  exp(-t/τ) * exp(-i ω t) = exp(-(a * t)).

The truncated integral can be evaluated in closed form using `integral_exp_smul_neg`,
then the `B → ∞` limit is obtained from `tendsto_exp_neg_mul_ofReal_atTop`.
-/

/-! ### Laplace transform limit and transfer-function bridge -/

/-- The complex exponent `a = (1/τ) + i ω` appearing in the Debye kernel transform. -/
def laplaceExponent (H : CaldeiraLeggett.TransferFunction) (ω : ℝ) : ℂ :=
  ((1 / H.τ : ℝ) : ℂ) + Complex.I * (ω : ℂ)


/-- Truncated Debye-kernel response tends to its closed form as `B → ∞`. -/
theorem kernel_response_limit (H : CaldeiraLeggett.TransferFunction) (ω : ℝ) :
    Filter.Tendsto (fun B => kernel_response_trunc H ω B) Filter.atTop
      (nhds ((H.Δ : ℂ) / ((1 : ℂ) + Complex.I * (ω : ℂ) * (H.τ : ℂ)))) := by
  -- Abbreviate `a = (1/τ) + iω`.
  set a : ℂ := laplaceExponent H ω with ha_def

  have ha_re : 0 < a.re := by
    have h : 0 < (1 / H.τ) := one_div_pos.2 H.τ_pos
    -- `a.re = 1/τ` since `Re(iω)=0`.
    simpa [ha_def, laplaceExponent] using h

  have ha : a ≠ 0 := by
    have hne : a.re ≠ 0 := ne_of_gt ha_re
    intro h0
    apply hne
    simpa [h0]

  -- Closed form for each truncation bound `B`.
  have hclosed (B : ℝ) :
      kernel_response_trunc H ω B =
        (H.Δ / H.τ : ℂ) * ((Complex.exp (B • (-a)) - 1) * (-a)⁻¹) := by
    -- Rewrite the integrand into the `exp (t • (-a))` shape and apply `integral_exp_smul_neg`.
    unfold kernel_response_trunc
    -- Push the real kernel into `ℂ`, and turn `Real.exp` into `Complex.exp`.
    simp_rw [debye_kernel]
    simp_rw [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_exp]
    -- Combine the two exponentials.
    simp_rw [← Complex.exp_add, ← mul_assoc, ← mul_left_comm, ← mul_comm]
    -- Pull out the constant factor and evaluate the remaining exponential integral.
    -- (At this point the integrand is exactly `exp (t • (-a))` after simp.)
    simp [ha_def, laplaceExponent, Complex.real_smul, intervalIntegral.integral_const_mul,
      integral_exp_smul_neg a ha B, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm,
      add_comm]

  -- Reduce to the closed form and take `B → ∞`.
  have hExp :
      Filter.Tendsto (fun B : ℝ => Complex.exp (B • (-a))) Filter.atTop (nhds (0 : ℂ)) := by
    -- `B • (-a) = -((B:ℂ) * a)`, and `Re(a) > 0`.
    have :=
      tendsto_exp_neg_mul_ofReal_atTop a ha_re
    simpa [Complex.real_smul, mul_assoc, mul_left_comm, mul_comm] using this

  have hExpSub :
      Filter.Tendsto (fun B : ℝ => Complex.exp (B • (-a)) - (1 : ℂ)) Filter.atTop (nhds (-1 : ℂ)) :=
    (hExp.sub tendsto_const_nhds)

  have hExpMul :
      Filter.Tendsto (fun B : ℝ => (Complex.exp (B • (-a)) - (1 : ℂ)) * (-a)⁻¹) Filter.atTop
        (nhds ((-1 : ℂ) * (-a)⁻¹)) :=
    (Filter.Tendsto.mul_const (-a)⁻¹ hExpSub)

  have hMain :
      Filter.Tendsto (fun B : ℝ => (H.Δ / H.τ : ℂ) * ((Complex.exp (B • (-a)) - 1) * (-a)⁻¹))
        Filter.atTop (nhds ((H.Δ / H.τ : ℂ) * ((-1 : ℂ) * (-a)⁻¹))) :=
    (Filter.Tendsto.const_mul (H.Δ / H.τ : ℂ) hExpMul)

  -- Rewrite the limit into the desired `Δ / (1 + iωτ)` form.
  have hlim_simplify :
      (H.Δ / H.τ : ℂ) * ((-1 : ℂ) * (-a)⁻¹) =
        (H.Δ : ℂ) / ((1 : ℂ) + Complex.I * (ω : ℂ) * (H.τ : ℂ)) := by
    -- `(-1) * (-a)⁻¹ = a⁻¹`, then regroup as a division by `τ*a = 1 + iωτ`.
    have : ((-1 : ℂ) * (-a)⁻¹) = a⁻¹ := by
      -- `(-a)⁻¹ = -(a⁻¹)`
      simp
    -- Rewrite `(Δ/τ) * a⁻¹` as `Δ / (τ * a)`, and compute `τ * a`.
    -- Use `ha_def` to expand `a = (1/τ) + iω`.
    -- `τ * ((1/τ) + iω) = 1 + iωτ`.
    -- Finally, cast `Δ/τ` into `ℂ` consistently.
    simp [this, ha_def, laplaceExponent, div_div, div_eq_mul_inv, mul_add, add_mul,
      mul_assoc, mul_left_comm, mul_comm]

  -- Assemble the tendsto statement.
  have hMain' :
      Filter.Tendsto (fun B : ℝ => kernel_response_trunc H ω B) Filter.atTop
        (nhds ((H.Δ : ℂ) / ((1 : ℂ) + Complex.I * (ω : ℂ) * (H.τ : ℂ)))) := by
    -- Rewrite by the pointwise closed form, then apply `hMain`.
    have hcongr :
        (fun B : ℝ => kernel_response_trunc H ω B) =
          fun B : ℝ => (H.Δ / H.τ : ℂ) * ((Complex.exp (B • (-a)) - 1) * (-a)⁻¹) := by
      funext B
      simpa [hclosed B]
    -- Transfer the limit.
    simpa [hcongr, hlim_simplify] using hMain

  exact hMain'


/-- `transfer_function_complex` is exactly the Debye single-pole transfer function form. -/
theorem transfer_function_eq_one_plus_kernel (H : CaldeiraLeggett.TransferFunction) (ω : ℝ) :
    transfer_function_complex H ω =
      (1 : ℂ) + (H.Δ : ℂ) / ((1 : ℂ) + Complex.I * (ω : ℂ) * (H.τ : ℂ)) := by
  simp [transfer_function_complex]


/-- The paper’s real-valued response function is the real part of the complex transfer function. -/
theorem response_function_is_real_part (H : CaldeiraLeggett.TransferFunction) (ω : ℝ) :
    CaldeiraLeggett.response_function H ω = (transfer_function_complex H ω).re := by
  -- Unfold both sides.
  unfold CaldeiraLeggett.response_function transfer_function_complex
  -- Let the complex denominator be `w = 1 + i ω τ`.
  set w : ℂ := (1 : ℂ) + Complex.I * (ω : ℂ) * (H.τ : ℂ) with hw
  have wre : w.re = 1 := by
    -- `Re(i * real) = 0`.
    simp [hw, mul_assoc, mul_left_comm, mul_comm]
  have wnormSq : Complex.normSq w = 1 + (ω * H.τ) ^ (2 : ℕ) := by
    -- `normSq w = w.re^2 + w.im^2`, and here `w.re = 1`, `w.im = ωτ`.
    -- We compute directly using `normSq_apply`.
    have : w.im = ω * H.τ := by
      simp [hw, mul_assoc, mul_left_comm, mul_comm]
    -- Expand `normSq` and simplify.
    -- Use `pow_two` (as `x^2 = x*x`) in the reverse direction.
    calc
      Complex.normSq w = w.re * w.re + w.im * w.im := by
        simpa [Complex.normSq_apply]
      _ = (1 : ℝ) * 1 + (ω * H.τ) * (ω * H.τ) := by
        simp [wre, this]
      _ = 1 + (ω * H.τ) ^ (2 : ℕ) := by
        simp [pow_two, mul_assoc]

  -- Reduce the real part using `Complex.div_re`.
  -- Since `H.Δ` is real, its imaginary part is 0.
  have hdiv :
      ((H.Δ : ℂ) / w).re = H.Δ / (1 + (ω * H.τ) ^ (2 : ℕ)) := by
    -- Apply `div_re` and simplify with `wre` and `wnormSq`.
    simp [Complex.div_re, wre, wnormSq, hw, mul_assoc, mul_left_comm, mul_comm, add_assoc,
      add_left_comm, add_comm]

  -- Finish: real part of `1 + z` is `1 + Re(z)`.
  -- Note: `simp` can unfold `.re` of addition definitionaly once `hdiv` is in place.
  -- We rewrite the divisor `w` back into the original denominator.
  simp [hw, hdiv, Complex.add_re]

end

end CausalKernelChain
end Gravity
end IndisputableMonolith
