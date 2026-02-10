import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Cost.FunctionalEquation
import IndisputableMonolith.Foundation.DAlembert.CurvatureGate
import IndisputableMonolith.Foundation.DAlembert.Counterexamples
import IndisputableMonolith.Relativity.Calculus.FunctionalEquationDeriv

/-!
# The Fourth Gate: d'Alembert Structure

This module formalizes the **Fourth Gate**: the d'Alembert structure condition.

## Relation to Gate 3 (Curvature)

In the Option~A formulation used in the paper, Gate~3 is a \emph{normalized} closure:
the hyperbolic branch is assumed directly as the ODE `G''(t) = G(t) + 1`.
Together with symmetry (evenness) and calibration, that already forces
`G(t) = cosh(t) - 1`. Consequently the shifted log-lift `H = G + 1 = cosh`
automatically satisfies the d'Alembert functional equation.

So, in that formulation, ``Gate 4'' is not an additional restriction beyond Gate~3;
it is a derived structure and a convenient cross-check.

We keep this module explicit because it packages the classical functional-equation
viewpoint (Aczél's classification theorem) as a compact certificate path in Lean.

## Historical Note

The d'Alembert functional equation `f(x+y) + f(x-y) = 2f(x)f(y)` was studied by
Jean le Rond d'Alembert in the 18th century. Its continuous solutions are exactly
`cosh(λx)` for λ ∈ ℝ. This is a classical result in functional equation theory.
-/

namespace IndisputableMonolith
namespace Foundation
namespace DAlembert
namespace FourthGate

open Real Cost CurvatureGate

/-! ## Definition of the Fourth Gate -/

/-- **d'Alembert Structure**: A function H satisfies the d'Alembert functional equation. -/
def SatisfiesDAlembert (H : ℝ → ℝ) : Prop :=
  (H 0 = 1) ∧ (∀ t u : ℝ, H (t + u) + H (t - u) = 2 * H t * H u)

/-- The d'Alembert structure gate for a cost function F:
    The shifted log-lift H(t) = F(eᵗ) + 1 satisfies d'Alembert. -/
def HasDAlembert Structure (F : ℝ → ℝ) : Prop :=
  SatisfiesDAlembert (fun t => F (Real.exp t) + 1)

/-! ## Canonical Solutions -/

/-- cosh satisfies the d'Alembert equation. -/
theorem cosh_satisfies_dAlembert : SatisfiesDAlembert Real.cosh := by
  constructor
  · exact Real.cosh_zero
  · intro t u
    have h1 := Real.cosh_add t u
    have h2 := Real.cosh_sub t u
    linarith

/-- Jcost has d'Alembert structure. -/
theorem Jcost_has_dAlembert_structure : HasDAlembert Structure Cost.Jcost := by
  unfold HasDAlembert Structure SatisfiesDAlembert
  constructor
  · simp [Cost.Jcost, Real.exp_zero]
  · intro t u
    have hH : ∀ s, Cost.Jcost (Real.exp s) + 1 = Real.cosh s := by
      intro s
      simp only [Cost.Jcost]
      have h := Real.cosh_eq s
      linarith
    simp only [hH]
    have hcosh := cosh_satisfies_dAlembert.2 t u
    exact hcosh

/-! ## d'Alembert Classification Theorem -/

/-- **Theorem (d'Alembert Classification)**: If H is C², satisfies d'Alembert,
    H(0) = 1, H'(0) = 0, and H''(0) = λ², then H(t) = cosh(λt).

    **Proof**:
    1. From d'Alembert Eq: H(t+u) + H(t-u) = 2 H(t) H(u)
    2. Differentiating twice w.r.t u and setting u=0 gives: H''(t) = H''(0) H(t) = λ² H(t)
    3. The unique solution to H'' = λ²H with H(0)=1, H'(0)=0 is cosh(λt). -/
theorem dAlembert_classification :
    ∀ H : ℝ → ℝ, ∀ λ : ℝ,
    SatisfiesDAlembert H →
    ContDiff ℝ 2 H →
    deriv H 0 = 0 →
    deriv (deriv H) 0 = λ ^ 2 →
    ∀ t, H t = Real.cosh (λ * t) := by
  intro H λ hDA hSmooth hDeriv0 hCalib t
  -- 1. Derive the ODE H'' = λ² H using dalembert_deriv_ode
  have h_ode : ∀ x, deriv (deriv H) x = λ ^ 2 * H x := by
    intro x
    rw [← hCalib]
    apply IndisputableMonolith.Relativity.Calculus.dalembert_deriv_ode H hSmooth hDA.2

  -- 2. Define the candidate solution C(t) = cosh(λt)
  let C := fun x => Real.cosh (λ * x)

  -- 3. Show C satisfies the same ODE: C'' = λ² C
  have hC_ode : ∀ x, deriv (deriv C) x = λ ^ 2 * C x := by
    intro x
    -- C(x) = cosh(λx)
    -- C'(x) = λ sinh(λx)
    -- C''(x) = λ² cosh(λx) = λ² C(x)
    have h1 : deriv C x = λ * Real.sinh (λ * x) := by
      have hd : HasDerivAt C (λ * Real.sinh (λ * x)) x := by
        have h := Real.hasDerivAt_cosh (λ * x)
        have hc : HasDerivAt (fun y => λ * y) λ x := hasDerivAt_id x |>.const_mul λ
        exact h.comp x hc
      exact hd.deriv
    have h2 : deriv (fun y => λ * Real.sinh (λ * y)) x = λ ^ 2 * Real.cosh (λ * x) := by
      have hd : HasDerivAt (fun y => λ * Real.sinh (λ * y)) (λ ^ 2 * Real.cosh (λ * x)) x := by
        have h := Real.hasDerivAt_sinh (λ * x)
        have hc : HasDerivAt (fun y => λ * y) λ x := hasDerivAt_id x |>.const_mul λ
        have h' := h.comp x hc
        exact h'.const_mul λ
      exact hd.deriv
    calc deriv (deriv C) x = deriv (fun y => λ * Real.sinh (λ * y)) x := by
           congr 1; ext y; exact (show deriv C y = λ * Real.sinh (λ * y) by
             have hd : HasDerivAt C (λ * Real.sinh (λ * y)) y := by
               have h := Real.hasDerivAt_cosh (λ * y)
               have hc : HasDerivAt (fun z => λ * z) λ y := hasDerivAt_id y |>.const_mul λ
               exact h.comp y hc
             exact hd.deriv)
         _ = λ ^ 2 * Real.cosh (λ * x) := h2
         _ = λ ^ 2 * C x := rfl

  -- 4. Show same initial conditions: C(0) = 1, C'(0) = 0
  have hC0 : C 0 = 1 := by simp [C, Real.cosh_zero]
  have hCderiv0 : deriv C 0 = 0 := by
    have hd : HasDerivAt C (λ * Real.sinh (λ * 0)) 0 := by
      have h := Real.hasDerivAt_cosh (λ * 0)
      have hc : HasDerivAt (fun y => λ * y) λ 0 := hasDerivAt_id 0 |>.const_mul λ
      exact h.comp 0 hc
    rw [hd.deriv, Real.sinh_zero, mul_zero]

  -- 5. ODE uniqueness via ode_zero_uniqueness from Cost.FunctionalEquation
  -- Define D = H - C. Show D'' = λ² D with D(0) = 0, D'(0) = 0, hence D = 0.
  let D := fun x => H x - C x
  have hD_diff : ContDiff ℝ 2 D := by
    apply ContDiff.sub hSmooth
    apply Real.contDiff_cosh.comp
    exact contDiff_const.mul contDiff_id

  have hD_ode : ∀ x, deriv (deriv D) x = λ ^ 2 * D x := by
    intro x
    have h1 : deriv D = fun y => deriv H y - deriv C y := by
      ext y
      apply deriv_sub (hSmooth.differentiable le_rfl).differentiableAt
      have : DifferentiableAt ℝ C y := by
        apply DifferentiableAt.comp y Real.differentiable_cosh.differentiableAt
        apply DifferentiableAt.const_mul differentiableAt_id
      exact this
    have h2 : deriv (deriv D) x = deriv (deriv H) x - deriv (deriv C) x := by
      rw [h1]
      apply deriv_sub
      · exact (hSmooth.iterate_deriv 1 1).differentiable le_rfl |>.differentiableAt
      · -- C = cosh(λ·) so C' = λ sinh(λ·) which is differentiable
        have hC'_diff : DifferentiableAt ℝ (fun y => λ * Real.sinh (λ * y)) x := by
          apply DifferentiableAt.const_mul
          apply DifferentiableAt.comp x Real.differentiable_sinh.differentiableAt
          exact DifferentiableAt.const_mul differentiableAt_id λ
        convert hC'_diff
        ext y
        have hd : HasDerivAt C (λ * Real.sinh (λ * y)) y := by
          have h := Real.hasDerivAt_cosh (λ * y)
          have hc : HasDerivAt (fun z => λ * z) λ y := hasDerivAt_id y |>.const_mul λ
          exact h.comp y hc
        exact hd.deriv
    rw [h2, h_ode, hC_ode]
    ring

  have hD0 : D 0 = 0 := by simp [D, hDA.1, hC0]
  have hDderiv0 : deriv D 0 = 0 := by
    have h1 : deriv D = fun y => deriv H y - deriv C y := by
      ext y
      apply deriv_sub (hSmooth.differentiable le_rfl).differentiableAt
      have : DifferentiableAt ℝ C y := by
        apply DifferentiableAt.comp y Real.differentiable_cosh.differentiableAt
        apply DifferentiableAt.const_mul differentiableAt_id
      exact this
    rw [h1, hDeriv0, hCderiv0, sub_zero]

  -- Use ODE zero uniqueness: y'' = λ² y with y(0) = y'(0) = 0 implies y = 0
  -- For λ ≠ 0, rescale: let E(s) = D(s/λ), then E'' = E with E(0) = E'(0) = 0
  -- For λ = 0, the ODE is D'' = 0 with D(0) = D'(0) = 0, so D = 0 trivially
  have h_unique : H t = C t := by
    by_cases hλ : λ = 0
    · -- λ = 0 case: H'' = 0 and C(t) = cosh(0) = 1
      simp only [hλ, zero_mul, Real.cosh_zero, C] at *
      have hH_const : ∀ x, H x = 1 := by
        -- H'' = 0 with H(0) = 1, H'(0) = 0 implies H is constant = 1
        have h_ode' : ∀ x, deriv (deriv H) x = 0 := by intro x; simp [h_ode]
        -- Step 1: H' is constant (since H'' = 0)
        have hH'_const : ∀ x y, deriv H x = deriv H y := by
          have h_diff_H' : Differentiable ℝ (deriv H) := by
            apply (hSmooth.iterate_deriv 1 1).differentiable le_rfl
          intro x y
          have h_const_deriv : deriv (deriv H) = fun _ => 0 := by ext z; exact h_ode' z
          have h_deriv_zero : ∀ z, HasDerivAt (deriv H) 0 z := by
            intro z
            rw [← h_ode' z]
            exact h_diff_H'.hasDerivAt z
          -- Apply mean value theorem: if f' = 0 everywhere, then f is constant
          have := IsLocallyConstant.of_hasDeriv h_diff_H'.continuous h_deriv_zero
          rw [isLocallyConstant_iff_isOpen_fiber] at this
          -- Since ℝ is connected and deriv H is locally constant, it's constant
          exact this.eq_const x y
        -- Step 2: H' = 0 everywhere (since H'(0) = 0)
        have hH'_zero : ∀ x, deriv H x = 0 := by
          intro x
          rw [hH'_const x 0, hDeriv0]
        -- Step 3: H is constant = H(0) = 1 (since H' = 0)
        intro x
        have h_diff_H : Differentiable ℝ H := hSmooth.differentiable le_rfl
        have h_deriv_zero : ∀ z, HasDerivAt H 0 z := by
          intro z
          rw [← hH'_zero z]
          exact h_diff_H.hasDerivAt z
        have := IsLocallyConstant.of_hasDeriv h_diff_H.continuous h_deriv_zero
        rw [isLocallyConstant_iff_isOpen_fiber] at this
        rw [this.eq_const x 0, hDA.1]
      exact hH_const t
    · -- λ ≠ 0 case: use rescaling and ode_zero_uniqueness
      have hDt : D t = 0 := by
        -- Define E(s) = D(s/λ), then E'' = E with E(0) = E'(0) = 0
        let E := fun s => D (s / λ)

        -- Show E is C²
        have hE_diff : ContDiff ℝ 2 E := by
          apply hD_diff.comp
          apply contDiff_const.div contDiff_id (fun _ => hλ)

        -- Show E'' = λ⁻² D''(s/λ) = λ⁻² · λ² D(s/λ) = D(s/λ) = E
        have hE_ode : ∀ s, deriv (deriv E) s = E s := by
          intro s
          -- E'(s) = D'(s/λ) · (1/λ)
          have hE' : deriv E s = deriv D (s / λ) / λ := by
            have hD_diff1 : Differentiable ℝ D := hD_diff.differentiable le_rfl
            have h_chain : HasDerivAt E (deriv D (s / λ) / λ) s := by
              have h1 : HasDerivAt D (deriv D (s / λ)) (s / λ) := hD_diff1.hasDerivAt (s / λ)
              have h2 : HasDerivAt (fun x => x / λ) (1 / λ) s := by
                have := hasDerivAt_id s
                exact this.div_const λ
              have h := h1.comp s h2
              simp only [mul_div_assoc, one_div] at h ⊢
              convert h using 1
              ring
            exact h_chain.deriv
          -- E''(s) = D''(s/λ) · (1/λ)²
          have hE'' : deriv (deriv E) s = deriv (deriv D) (s / λ) / (λ ^ 2) := by
            have hD'_diff : Differentiable ℝ (deriv D) := by
              apply (hD_diff.iterate_deriv 1 1).differentiable le_rfl
            have h_E'_eq : deriv E = fun x => deriv D (x / λ) / λ := by
              ext x
              have hD_diff1 : Differentiable ℝ D := hD_diff.differentiable le_rfl
              have h_chain : HasDerivAt E (deriv D (x / λ) / λ) x := by
                have h1 : HasDerivAt D (deriv D (x / λ)) (x / λ) := hD_diff1.hasDerivAt (x / λ)
                have h2 : HasDerivAt (fun y => y / λ) (1 / λ) x := (hasDerivAt_id x).div_const λ
                have h := h1.comp x h2
                simp only [mul_div_assoc, one_div] at h ⊢
                convert h using 1
                ring
              exact h_chain.deriv
            rw [h_E'_eq]
            -- Now differentiate D'(s/λ) / λ
            have h_chain' : HasDerivAt (fun x => deriv D (x / λ) / λ) (deriv (deriv D) (s / λ) / (λ ^ 2)) s := by
              have h1 : HasDerivAt (deriv D) (deriv (deriv D) (s / λ)) (s / λ) := hD'_diff.hasDerivAt (s / λ)
              have h2 : HasDerivAt (fun x => x / λ) (1 / λ) s := (hasDerivAt_id s).div_const λ
              have h := (h1.comp s h2).div_const λ
              simp only [mul_div_assoc, one_div] at h ⊢
              convert h using 1
              field_simp
              ring
            exact h_chain'.deriv
          rw [hE'']
          -- D''(s/λ) = λ² D(s/λ) = λ² E(s)
          rw [hD_ode (s / λ)]
          simp only [E]
          field_simp
          ring

        -- Show E(0) = D(0) = 0
        have hE0 : E 0 = 0 := by simp only [E, zero_div, hD0]

        -- Show E'(0) = D'(0)/λ = 0
        have hE'0 : deriv E 0 = 0 := by
          have hD_diff1 : Differentiable ℝ D := hD_diff.differentiable le_rfl
          have h_chain : HasDerivAt E (deriv D (0 / λ) / λ) 0 := by
            have h1 : HasDerivAt D (deriv D (0 / λ)) (0 / λ) := hD_diff1.hasDerivAt (0 / λ)
            have h2 : HasDerivAt (fun x => x / λ) (1 / λ) 0 := (hasDerivAt_id 0).div_const λ
            have h := h1.comp 0 h2
            simp only [mul_div_assoc, one_div] at h ⊢
            convert h using 1
            ring
          rw [h_chain.deriv, zero_div, hDderiv0, zero_div]

        -- Apply ode_zero_uniqueness: E = 0
        have hE_zero := Cost.ode_zero_uniqueness E hE_diff hE_ode hE0 hE'0

        -- D(t) = E(λ * t) = 0
        have h_D_from_E : D t = E (λ * t) := by
          simp only [E]
          congr 1
          field_simp

        rw [h_D_from_E, hE_zero (λ * t)]

      simp [D] at hDt
      linarith [hDt]
  exact h_unique

/-- **Corollary**: With calibration H''(0) = 1, we get λ = 1, so H = cosh. -/
theorem dAlembert_with_unit_calibration (H : ℝ → ℝ)
    (hDA : SatisfiesDAlembert H)
    (hSmooth : ContDiff ℝ 2 H)
    (hDeriv0 : deriv H 0 = 0)
    (hCalib : deriv (deriv H) 0 = 1) :
    ∀ t, H t = Real.cosh t := by
  have h1sq : (1 : ℝ) = 1 ^ 2 := by norm_num
  rw [h1sq] at hCalib
  have := dAlembert_classification H 1 hDA hSmooth hDeriv0 hCalib
  simp only [one_mul] at this
  exact this

/-! ## d'Alembert Forces Canonical G -/

/-- d'Alembert structure + calibration forces G = cosh - 1. -/
theorem dAlembert_forces_Gcosh (G : ℝ → ℝ)
    (hDA : SatisfiesDAlembert (fun t => G t + 1))
    (hSmooth : ContDiff ℝ 2 G)
    (hNorm : G 0 = 0)
    (hEven : ∀ t, G (-t) = G t)
    (hCalib : deriv (deriv G) 0 = 1) :
    ∀ t, G t = Real.cosh t - 1 := by
  let H := fun t => G t + 1
  have hHsmooth : ContDiff ℝ 2 H := hSmooth.add contDiff_const
  have hHderiv0 : deriv H 0 = 0 := by
    have hderivH : deriv H = deriv G := by ext t; simp [H, deriv_add_const]
    rw [hderivH]
    have hGeven : (fun t => G (-t)) = G := funext hEven
    have hcomp : deriv (fun t => G (-t)) 0 = deriv G 0 := by simp only [hGeven]
    have hchain : deriv (fun t => G (-t)) 0 = -(deriv G 0) := by
      have heq : (fun t => G (-t)) = G ∘ (fun t => -t) := rfl
      rw [heq]
      have hGdiff : DifferentiableAt ℝ G 0 := hSmooth.differentiable le_rfl |>.differentiableAt
      rw [deriv_comp (0 : ℝ) (by simp only [neg_zero]; exact hGdiff) differentiable_neg.differentiableAt]
      simp only [neg_zero, deriv_neg', mul_neg_one]
    rw [hchain] at hcomp
    linarith
  have hHcalib : deriv (deriv H) 0 = 1 := by
    have h1 : deriv H = deriv G := by ext t; simp [H, deriv_add_const]
    have h2 : deriv (deriv H) = deriv (deriv G) := by simp [h1]
    rw [h2, hCalib]
  have hHcosh := dAlembert_with_unit_calibration H hDA hHsmooth hHderiv0 hHcalib
  intro t
  have := hHcosh t
  simp only [H] at this
  linarith

/-! ## The Counterexample Fails Gate 4 -/

/-- The quadratic log-lift H(t) = t²/2 + 1 does NOT satisfy d'Alembert. -/
theorem Hquad_not_dAlembert : ¬ SatisfiesDAlembert (fun t => t^2/2 + 1) := by
  intro ⟨_, hda⟩
  have h11 := hda 1 1
  norm_num at h11

/-- Fquad does NOT have d'Alembert structure. -/
theorem Fquad_not_dAlembert_structure : ¬ HasDAlembert Structure Counterexamples.Fquad := by
  intro h
  unfold HasDAlembert Structure at h
  have hH : (fun t => Counterexamples.Fquad (Real.exp t) + 1) = (fun t => t^2/2 + 1) := by
    ext t
    simp [Counterexamples.Fquad, Cost.F_ofLog, Counterexamples.Gquad, Real.log_exp]
  rw [hH] at h
  exact Hquad_not_dAlembert h

/-! ## Fourth Gate Summary -/

/-- **Fourth Gate Theorem**: Jcost satisfies d'Alembert structure; Fquad does not. -/
theorem fourth_gate_summary :
    HasDAlembert Structure Cost.Jcost ∧
    ¬ HasDAlembert Structure Counterexamples.Fquad :=
  ⟨Jcost_has_dAlembert_structure, Fquad_not_dAlembert_structure⟩

/-! ## Full Inevitability with Four Gates -/

/-- **Full Inevitability**: d'Alembert structure + structural axioms forces F = Jcost. -/
theorem dAlembert_forces_Jcost (F : ℝ → ℝ)
    (hNorm : F 1 = 0)
    (hSymm : ∀ x : ℝ, 0 < x → F x = F x⁻¹)
    (hSmooth : ContDiff ℝ 2 F)
    (hCalib : deriv (deriv (fun t => F (Real.exp t))) 0 = 1)
    (hDA : HasDAlembert Structure F) :
    ∀ x : ℝ, 0 < x → F x = Cost.Jcost x := by
  intro x hx
  let G := fun t => F (Real.exp t)
  have hGsmooth : ContDiff ℝ 2 G := hSmooth.comp Real.contDiff_exp
  have hGnorm : G 0 = 0 := by simp [G, hNorm]
  have hGeven : ∀ t, G (-t) = G t := by
    intro t
    simp only [G, Real.exp_neg]
    exact hSymm (Real.exp t) (Real.exp_pos t)
  have hGcosh := dAlembert_forces_Gcosh G hDA hGsmooth hGnorm hGeven hCalib
  have hFx : F x = G (Real.log x) := by simp [G, Real.exp_log hx]
  rw [hFx, hGcosh (Real.log x)]
  simp only [Cost.Jcost]
  have hcosh : Real.cosh (Real.log x) = (x + x⁻¹) / 2 := by
    rw [Real.cosh_eq, Real.exp_log hx, Real.exp_neg, Real.exp_log hx]
  linarith [hcosh]

end FourthGate
end DAlembert
end Foundation
end IndisputableMonolith
