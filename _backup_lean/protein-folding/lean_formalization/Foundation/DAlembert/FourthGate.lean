import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Foundation.DAlembert.CurvatureGate
import IndisputableMonolith.Foundation.DAlembert.Counterexamples

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

/-- **Axiom (d'Alembert Classification)**: If H is C², satisfies d'Alembert,
    H(0) = 1, H'(0) = 0, and H''(0) = λ², then H(t) = cosh(λt).

    This is Aczél's classification theorem: continuous solutions to d'Alembert
    are exactly cosh(λt) for some λ ∈ ℝ. -/
axiom dAlembert_classification :
    ∀ H : ℝ → ℝ, ∀ λ : ℝ,
    SatisfiesDAlembert H →
    ContDiff ℝ 2 H →
    deriv H 0 = 0 →
    deriv (deriv H) 0 = λ ^ 2 →
    ∀ t, H t = Real.cosh (λ * t)

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
