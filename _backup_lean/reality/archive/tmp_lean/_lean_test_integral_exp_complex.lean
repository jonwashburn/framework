import Mathlib

namespace Scratch

open scoped Real

open Complex

noncomputable section

-- Test: compute ∫_0^B exp(t • (-a)) dt in ℂ.

theorem integral_exp_smul_neg (a : ℂ) (ha : a ≠ 0) (B : ℝ) :
    ∫ t in (0:ℝ)..B, Complex.exp (t • (-a))
      = (Complex.exp (B • (-a)) - 1) * (-a)⁻¹ := by
  -- Use antiderivative F(t) = exp(t•(-a)) * (-a)⁻¹
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) B,
      HasDerivAt (fun t : ℝ => Complex.exp (t • (-a)) * (-a)⁻¹)
        (Complex.exp (x • (-a))) x := by
    intro x hx
    -- Derivative of inner: t ↦ t
    have h_id : HasDerivAt (fun t : ℝ => t) (1:ℝ) x := by
      simpa using (hasDerivAt_id x)
    -- t ↦ t • (-a)
    have h_inner : HasDerivAt (fun t : ℝ => t • (-a)) ((1:ℝ) • (-a)) x :=
      (HasDerivAt.smul_const (𝕜 := ℝ) (𝕜' := ℝ) (F := ℂ) (x := x) h_id (-a))
    have h_inner' : HasDerivAt (fun t : ℝ => t • (-a)) (-a) x := by
      simpa using h_inner

    -- exp ∘ inner
    have h_exp : HasDerivAt (fun t : ℝ => Complex.exp (t • (-a)))
        (Complex.exp (x • (-a)) * (-a)) x := by
      simpa [Function.comp] using ((Complex.hasDerivAt_exp (x • (-a))).comp x h_inner')

    -- multiply by (-a)⁻¹, then cancel
    have hmul : HasDerivAt (fun t : ℝ => (fun t => Complex.exp (t • (-a))) t * (-a)⁻¹)
        ((Complex.exp (x • (-a)) * (-a)) * (-a)⁻¹) x :=
      (HasDerivAt.mul_const (𝕜 := ℝ) (𝔸 := ℂ) (x := x) h_exp ((-a)⁻¹))

        -- simplify the derivative using a ≠ 0
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

  -- Rewrite F(B) - F(0) into the target form.
  have h0 : Complex.exp ((0:ℝ) • (-a)) = (1:ℂ) := by
    simp

  calc
    ∫ t in (0:ℝ)..B, Complex.exp (t • (-a))
        = Complex.exp (B • (-a)) * (-a)⁻¹ - Complex.exp ((0:ℝ) • (-a)) * (-a)⁻¹ := by
            simpa using hFTC
    _ = Complex.exp (B • (-a)) * (-a)⁻¹ - (1:ℂ) * (-a)⁻¹ := by
            simp [h0]
    _ = (Complex.exp (B • (-a)) - 1) * (-a)⁻¹ := by
            ring

end

end Scratch
