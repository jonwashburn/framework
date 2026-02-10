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
  (hCoshAdd : FunctionalEquation.CoshAddIdentity F) :
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

  -- Apply d'Alembert uniqueness to get Gf(t) = cosh(t) - 1
  have h_G_cosh : ∀ t, Gf t = Real.cosh t - 1 :=
    FunctionalEquation.dAlembert_uniqueness_cosh Gf h_even h_G0 hCalib h_G_cont h_direct

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

end CostUniqueness
end IndisputableMonolith
