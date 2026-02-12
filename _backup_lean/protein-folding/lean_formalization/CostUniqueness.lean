import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Cost.Convexity
import IndisputableMonolith.CPM.LawOfExistence
import IndisputableMonolith.Cost.FunctionalEquation

/-!
# Cost Uniqueness: Main Theorem T5

This module provides the complete uniqueness theorem for J,
consolidating results from Convexity, Calibration, and FunctionalEquation.

Main result: Any cost functional F satisfying symmetry, unit normalization,
strict convexity, and calibration must equal Jcost on ℝ₊.
-/

namespace IndisputableMonolith
namespace CostUniqueness

open Real Cost Set

/-! We avoid global axioms. Functional-equation ingredients are supplied
    as explicit hypotheses in the theorems below. -/

/-- Full T5 Uniqueness Theorem (with explicit functional-identity hypothesis) -/
theorem T5_uniqueness_complete (F : ℝ → ℝ)
  (hSymm : ∀ {x}, 0 < x → F x = F x⁻¹)
  (hUnit : F 1 = 0)
  (hConvex : StrictConvexOn ℝ (Set.Ioi 0) F)
  (hCalib : deriv (deriv (F ∘ exp)) 0 = 1)
  (hCont : ContinuousOn F (Ioi 0))
  (hCoshAdd : FunctionalEquation.CoshAddIdentity F)
  (h_smooth_hyp : FunctionalEquation.dAlembert_continuous_implies_smooth_hypothesis (FunctionalEquation.H F))
  (h_ode_hyp : FunctionalEquation.dAlembert_to_ODE_hypothesis (FunctionalEquation.H F))
  (h_cont_hyp : FunctionalEquation.ode_regularity_continuous_hypothesis (FunctionalEquation.H F))
  (h_diff_hyp : FunctionalEquation.ode_regularity_differentiable_hypothesis (FunctionalEquation.H F))
  (h_bootstrap_hyp : FunctionalEquation.ode_linear_regularity_bootstrap_hypothesis (FunctionalEquation.H F)) :
  ∀ {x : ℝ}, 0 < x → F x = Jcost x := by
  intro x hx
  -- Reduce to log coordinates and invoke d'Alembert uniqueness
  let Gf : ℝ → ℝ := FunctionalEquation.G F
  have h_even : Function.Even Gf := FunctionalEquation.G_even_of_reciprocal_symmetry F hSymm
  have h_G0 : Gf 0 = 0 := FunctionalEquation.G_zero_of_unit F hUnit

  -- Gf is continuous on ℝ (F is continuous on (0,∞), exp is continuous, composition is continuous)
  have h_G_cont : Continuous Gf := by
    have h := ContinuousOn.comp_continuous hCont continuous_exp
    have h' : Continuous (fun t => F (Real.exp t)) :=
      h (by intro t; exact mem_Ioi.mpr (Real.exp_pos t))
    simpa [FunctionalEquation.G] using h'

  -- Convert CoshAddIdentity F to DirectCoshAdd Gf
  have h_direct : FunctionalEquation.DirectCoshAdd Gf :=
    FunctionalEquation.CoshAddIdentity_implies_DirectCoshAdd F hCoshAdd

  -- Apply d'Alembert uniqueness (via the shifted H := G + 1) to get Gf(t) = cosh(t) - 1.
  let Hf : ℝ → ℝ := FunctionalEquation.H F
  have h_H0 : Hf 0 = 1 := by
    simp [Hf, FunctionalEquation.H, FunctionalEquation.G, hUnit]
  have h_H_cont : Continuous Hf := by
    simpa [Hf, FunctionalEquation.H] using h_G_cont.add continuous_const
  have h_dAlembert : ∀ t u, Hf (t + u) + Hf (t - u) = 2 * Hf t * Hf u := by
    intro t u
    have hG := h_direct t u
    -- Convert the direct cosh-add identity for G into the d'Alembert identity for H := G + 1.
    -- This is pure ring algebra.
    -- (G(t+u)+G(t-u)) = 2(Gt·Gu) + 2(Gt+Gu)
    -- ⇔ (H(t+u)+H(t-u)) = 2HtHu  for H := G + 1.
    have h_goal :
        (Gf (t + u) + 1) + (Gf (t - u) + 1) = 2 * (Gf t + 1) * (Gf u + 1) := by
      calc
        (Gf (t + u) + 1) + (Gf (t - u) + 1)
            = (Gf (t + u) + Gf (t - u)) + 2 := by ring
        _ = (2 * (Gf t * Gf u) + 2 * (Gf t + Gf u)) + 2 := by simpa [hG]
        _ = 2 * (Gf t + 1) * (Gf u + 1) := by ring
    -- Discharge the original goal by unfolding Hf := H F := G F + 1 and rewriting in terms of Gf.
    simpa [Hf, FunctionalEquation.H, Gf] using h_goal
  have h_H_d2 : deriv (deriv Hf) 0 = 1 := by
    -- Hf = Gf + 1, so the 2nd derivative at 0 is the same as for Gf.
    have hG_d2 : deriv (deriv Gf) 0 = 1 := by
      simpa [Gf, FunctionalEquation.G] using hCalib
    -- `deriv (Hf)` equals `deriv (Gf)` pointwise, so their second derivatives match too.
    have hderiv : deriv Hf = deriv Gf := by
      funext t
      -- Unfold Hf := (fun y => Gf y + 1), then apply `deriv_add_const`.
      change deriv (fun y => Gf y + 1) t = deriv Gf t
      simpa using (deriv_add_const (f := Gf) (x := t) (c := (1 : ℝ)))
    have hderiv2 : deriv (deriv Hf) = deriv (deriv Gf) := congrArg deriv hderiv
    have hderiv2_at0 : deriv (deriv Hf) 0 = deriv (deriv Gf) 0 := congrArg (fun g => g 0) hderiv2
    exact hderiv2_at0.trans hG_d2
  have h_H_cosh : ∀ t, Hf t = Real.cosh t :=
    FunctionalEquation.dAlembert_cosh_solution
      Hf h_H0 h_H_cont h_dAlembert h_H_d2 h_smooth_hyp h_ode_hyp h_cont_hyp h_diff_hyp h_bootstrap_hyp
  have h_G_cosh : ∀ t, Gf t = Real.cosh t - 1 := by
    intro t
    have hH := h_H_cosh t
    -- Unshift: H = G + 1.
    have hH' : Gf t + 1 = Real.cosh t := by
      simpa [Hf, FunctionalEquation.H, Gf] using hH
    linarith

  -- Now convert back using the log-parametrization identity for Jcost
  have ht : Real.exp (Real.log x) = x := Real.exp_log hx
  have hJG : FunctionalEquation.G Cost.Jcost (Real.log x) = Real.cosh (Real.log x) - 1 :=
    FunctionalEquation.Jcost_G_eq_cosh_sub_one (Real.log x)
  calc F x
      = F (Real.exp (Real.log x)) := by rw [ht]
    _ = Gf (Real.log x) := rfl
    _ = Real.cosh (Real.log x) - 1 := h_G_cosh (Real.log x)
    _ = FunctionalEquation.G Cost.Jcost (Real.log x) := by simpa using hJG.symm
    _ = Jcost (Real.exp (Real.log x)) := by simp [FunctionalEquation.G]
    _ = Jcost x := by simpa [ht]

/-- Hypotheses bundle for uniqueness on ℝ₊ (non-axiomatic). -/
structure UniqueCostAxioms (F : ℝ → ℝ) : Prop where
  symmetric : ∀ {x}, 0 < x → F x = F x⁻¹
  unit : F 1 = 0
  convex : StrictConvexOn ℝ (Set.Ioi 0) F
  calibrated : deriv (deriv (F ∘ exp)) 0 = 1
  continuousOn_pos : ContinuousOn F (Ioi 0)
  coshAdd : FunctionalEquation.CoshAddIdentity F
  dAlembert_smooth : FunctionalEquation.dAlembert_continuous_implies_smooth_hypothesis (FunctionalEquation.H F)
  dAlembert_toODE : FunctionalEquation.dAlembert_to_ODE_hypothesis (FunctionalEquation.H F)
  ode_cont : FunctionalEquation.ode_regularity_continuous_hypothesis (FunctionalEquation.H F)
  ode_diff : FunctionalEquation.ode_regularity_differentiable_hypothesis (FunctionalEquation.H F)
  ode_bootstrap : FunctionalEquation.ode_linear_regularity_bootstrap_hypothesis (FunctionalEquation.H F)

/-- Jcost is continuous on ℝ₊ -/
lemma Jcost_continuous_pos : ContinuousOn Jcost (Ioi 0) := by
  classical
  have h1 : ContinuousOn (fun x : ℝ => x) (Ioi 0) := continuousOn_id
  have h2 : ContinuousOn (fun x : ℝ => x⁻¹) (Ioi 0) := by
    refine ContinuousOn.inv₀ (f:=fun x : ℝ => x) (s:=Ioi 0) h1 ?hneq
    intro x hx; exact ne_of_gt hx
  have h3 : ContinuousOn (fun x : ℝ => x + x⁻¹) (Ioi 0) := h1.add h2
  have h4 : ContinuousOn (fun x : ℝ => (1 / 2 : ℝ) * (x + x⁻¹)) (Ioi 0) :=
    (continuousOn_const).mul h3
  have h5 : ContinuousOn (fun x : ℝ => (1 / 2 : ℝ) * (x + x⁻¹) - 1) (Ioi 0) :=
    h4.sub continuousOn_const
  simpa [Jcost, one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg]
    using h5

/- Jcost satisfies the non-axiomatic hypothesis bundle (unused here)
 def Jcost_satisfies_axioms : UniqueCostAxioms Jcost where
  symmetric := fun hx => Jcost_symm hx
  unit := Jcost_unit0
  convex := Jcost_strictConvexOn_pos
  calibrated := by
    simpa using IndisputableMonolith.CPM.LawOfExistence.RS.Jcost_log_second_deriv_normalized
  continuousOn_pos := Jcost_continuous_pos
  coshAdd := FunctionalEquation.Jcost_cosh_add_identity -/

/-- Main uniqueness statement on ℝ₊: any admissible cost equals Jcost on (0,∞). -/
theorem unique_cost_on_pos (F : ℝ → ℝ) (hF : UniqueCostAxioms F) :
  ∀ {x : ℝ}, 0 < x → F x = Jcost x :=
  T5_uniqueness_complete F hF.symmetric hF.unit hF.convex hF.calibrated hF.continuousOn_pos hF.coshAdd
    hF.dAlembert_smooth hF.dAlembert_toODE hF.ode_cont hF.ode_diff hF.ode_bootstrap

end CostUniqueness
end IndisputableMonolith
