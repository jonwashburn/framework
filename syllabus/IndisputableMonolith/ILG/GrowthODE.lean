import Mathlib
import IndisputableMonolith.ILG.Kernel
import IndisputableMonolith.ILG.Reciprocity

namespace IndisputableMonolith
namespace ILG

open Real

/-- The prefactor for the first-order ILG growth correction in EdS background.
    Derived from plugging D = a(1 + B a^alpha) into the growth ODE. -/
noncomputable def growth_prefactor (alpha C : ℝ) : ℝ :=
  (3 * C) / (2 * alpha^2 + 5 * alpha)

/-- The closed-form ILG growth factor D(a, k) in EdS background (first-order in C). -/
noncomputable def growth_eds_ilg (P : KernelParams) (k a : ℝ) : ℝ :=
  a * (1 + (growth_prefactor P.alpha P.C) * (a / (k * P.tau0)) ^ P.alpha)

/-- Growth rate f = d ln D / d ln a for the ILG growth factor. -/
noncomputable def f_growth_eds_ilg (P : KernelParams) (k a : ℝ) : ℝ :=
  let Xinv := a / (k * P.tau0)
  let B := growth_prefactor P.alpha P.C
  (1 + B * (1 + P.alpha) * Xinv ^ P.alpha) / (1 + B * Xinv ^ P.alpha)

/-- The ILG-modified growth ODE in EdS background (Target B).
    Using ln(a) as the independent variable:
    D'' + (1/2) D' - (3/2) w(a,k) D = 0 -/
def GrowthODE_ILG (P : KernelParams) (k : ℝ) (D_func : ℝ → ℝ) : Prop :=
  ∀ a, 0 < a →
    let w := kernel P k a
    -- Expressed in terms of derivatives w.r.t a:
    -- a² D'' + (3/2) a D' - (3/2) w D = 0
    a^2 * (deriv (deriv D_func) a) + (3/2 : ℝ) * a * (deriv D_func a) - (3/2 : ℝ) * w * D_func a = 0

/-- Theorem: The closed-form growth factor satisfies the ILG-modified growth ODE
    to first order in C (neglecting O(C²) terms). -/
theorem growth_satisfies_ode (P : KernelParams) (k : ℝ) (hk : 0 < k) :
    let B := growth_prefactor P.alpha P.C
    let D := fun a => a * (1 + B * (a / (k * P.tau0)) ^ P.alpha)
    ∀ a, 0 < a →
      (0.01 : ℝ) ≤ (a / (k * P.tau0)) →
      let w := kernel P k a
      let Xinv := (a / (k * P.tau0))
      let error_term := (3/2 : ℝ) * P.C * B * Xinv ^ (2 * P.alpha) * a
      a^2 * (deriv (deriv D) a) + (3/2 : ℝ) * a * (deriv D a) - (3/2 : ℝ) * w * D a + error_term = 0 := by
  intro B D a ha hXinv_large
  unfold growth_prefactor kernel
  set C := P.C
  set α := P.alpha
  set τ₀ := P.tau0
  set Xinv := a / (k * τ₀)
  -- D(a) = a + B * (k*τ₀)^(-α) * a^(1+α)
  have hD : D = fun a => a + B * (k * τ₀) ^ (-α) * a ^ (1 + α) := by
    funext a'; simp [D]
    rw [div_rpow (le_of_lt ha) (mul_nonneg (le_of_lt hk) (le_of_lt P.tau0_pos))]
    rw [Real.rpow_neg (mul_pos hk P.tau0_pos)]
    ring
  -- Compute derivatives
  have h_deriv_D : deriv D a = 1 + B * (1 + α) * Xinv ^ α := by
    rw [hD]
    rw [deriv_add differentiableAt_id']
    · simp
      rw [deriv_mul_const]
      · rw [deriv_rpow_const (1 + α)]
        · field_simp [Xinv]
          ring
        · exact Or.inl ha.ne'
      · exact differentiableAt_rpow_const (1 + α) (Or.inl ha.ne')
    · apply DifferentiableAt.mul_const
      exact differentiableAt_rpow_const (1 + α) (Or.inl ha.ne')

  have h_deriv_2_D : deriv (deriv D) a = B * α * (1 + α) * Xinv ^ α / a := by
    -- D(a) = a + B * (k*τ₀)^(-α) * a^(1+α)
    -- deriv D = (fun a' => 1 + B * (1 + α) * (k*τ₀)^(-α) * a'^α)
    have h_deriv_eq : ∀ᶠ a' in 𝓝 a, deriv D a' = 1 + B * (1 + α) * (k * τ₀) ^ (-α) * a' ^ α := by
      filter_upwards [self_mem_nhds ha]
      intro a' ha'
      rw [hD, deriv_add differentiableAt_id']
      · simp
        rw [deriv_mul_const]
        · rw [deriv_rpow_const (1 + α)]
          · field_simp
            ring
          · exact Or.inl ha'.ne'
        · exact differentiableAt_rpow_const (1 + α) (Or.inl ha'.ne')
      · apply DifferentiableAt.mul_const
        exact differentiableAt_rpow_const (1 + α) (Or.inl ha'.ne')

    rw [deriv_congr_ev h_deriv_eq]
    rw [deriv_add (differentiableAt_const 1)]
    · simp
      rw [deriv_mul_const]
      · rw [deriv_rpow_const α]
        · field_simp [Xinv]
          ring
        · exact Or.inl ha.ne'
      · exact differentiableAt_rpow_const α (Or.inl ha.ne')
    · apply DifferentiableAt.mul_const
      exact differentiableAt_rpow_const α (Or.inl ha.ne')

  -- Plug in and simplify

  -- Plug in and simplify
  simp only [h_deriv_D, h_deriv_2_D]
  unfold kernel
  have hmax : max 0.01 Xinv = Xinv := max_eq_right hXinv_large
  rw [hmax]
  field_simp [ha.ne']
  ring_nf
  simp [error_term]
  rw [mul_assoc, ← mul_add]
  convert mul_zero (a * Xinv ^ α)
  field_simp
  ring

/-- Theorem: The ILG growth rate f(a,k) reduces to 1 in the GR limit (C=0). -/
theorem f_growth_gr_limit (P : KernelParams) (hC : P.C = 0) (k a : ℝ) (ha : 0 < a) :
    f_growth_eds_ilg P k a = 1 := by
  simp [f_growth_eds_ilg, growth_prefactor, hC]

/-- Proof of the X-reciprocity identity for the growth factor D(a, k) (Target C). -/
theorem growth_x_reciprocity (P : KernelParams) (k a : ℝ) (ha : 0 < a) (hk : 0 < k) :
    let D := growth_eds_ilg P k
    let Q := fun a' k' => growth_eds_ilg P k' a' / a'
    a * (deriv (fun a' => Q a' k) a) = - k * (deriv (fun k' => Q a k') k) := by
  -- Q(a, k) = 1 + B * (a / (k * tau0)) ^ alpha
  -- Let Q_tilde(X) = 1 + B * (1/X)^alpha where X = k*tau0/a
  set B := growth_prefactor P.alpha P.C
  let Q_tilde := fun x => 1 + B * (1 / x) ^ P.alpha
  have h_eq : ∀ a' k', 0 < a' → 0 < k' → (growth_eds_ilg P k' a' / a') = Q_tilde (X_var k' a' P.tau0) := by
    intro a' k' ha' hk'
    simp [growth_eds_ilg, Q_tilde, X_var]
    field_simp [ha', hk', P.tau0_pos.ne']
  -- Application of the reciprocity identity from Reciprocity.lean
  have h_diff : DifferentiableAt ℝ Q_tilde (X_var k a P.tau0) := by
    apply DifferentiableAt.const_add
    apply DifferentiableAt.mul_const
    apply DifferentiableAt.rpow
    · apply DifferentiableAt.const_div
      · exact differentiableAt_id'
      · exact (X_var k a P.tau0_pos).ne' -- non-zero
    · exact differentiableAt_const _
    · apply Or.inl; apply div_pos; apply mul_pos hk P.tau0_pos; exact ha
  exact x_reciprocity_identity P.tau0 Q_tilde a k ha.ne' hk.ne' h_diff

end ILG
end IndisputableMonolith
