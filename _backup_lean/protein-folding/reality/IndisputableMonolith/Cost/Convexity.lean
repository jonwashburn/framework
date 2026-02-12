import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Hyperbolic
import Mathlib.Analysis.SpecialFunctions.Trigonometric
import IndisputableMonolith.Cost.Jlog
import IndisputableMonolith.Cost.JcostCore

/-!
# Convexity of J

This module proves that:
1. Jlog(t) = cosh t - 1 is strictly convex on ℝ
2. Jcost(x) = ½(x + x⁻¹) - 1 is strictly convex on ℝ₊

These are foundational for the uniqueness theorem T5.
-/

namespace IndisputableMonolith
namespace Cost

open Real Set

open scoped Real

/-- Strict convexity of `Real.cosh` on the whole line. -/
theorem strictConvexOn_cosh : StrictConvexOn ℝ univ Real.cosh := by
  refine
    (StrictMonoOn.strictConvexOn_of_deriv (s := (Set.univ : Set ℝ)) convex_univ
      (Real.continuous_cosh.continuousOn)) ?_
  have hsinh : StrictMono fun x : ℝ => Real.sinh x := by
    simpa using sinh_strictMono
  simpa [interior_univ, deriv_cosh] using hsinh.strictMonoOn

/-- Strict convexity of `Jlog` on `ℝ`. -/
theorem Jlog_strictConvexOn : StrictConvexOn ℝ univ Jlog := by
  have h := StrictConvexOn.add_const (f := fun x : ℝ => Real.cosh x) strictConvexOn_cosh (-1 : ℝ)
  convert h using 1
  ext x; simp [Jlog_eq_cosh_sub_one, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

private def JcostDeriv (x : ℝ) : ℝ := (1 - x⁻²) / 2

private lemma hasDerivAt_Jcost {x : ℝ} (hx : 0 < x) :
    HasDerivAt Jcost (JcostDeriv x) x := by
  have hxne : (x : ℝ) ≠ 0 := ne_of_gt hx
  have hsum : HasDerivAt (fun y : ℝ => y + y⁻¹) (1 - x⁻²) x := by
    have h_id := HasDerivAt.id (ℝ := ℝ) x
    have h_inv := hasDerivAt_inv (x := x) hxne
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, pow_two]
      using h_id.add h_inv
  have havg : HasDerivAt (fun y : ℝ => (y + y⁻¹) / 2) (JcostDeriv x) x := by
    simpa [JcostDeriv, one_div] using hsum.const_mul ((1 : ℝ) / 2)
  simpa [Jcost] using havg.sub_const 1

private lemma deriv_Jcost {x : ℝ} (hx : 0 < x) :
    deriv Jcost x = JcostDeriv x := (hasDerivAt_Jcost hx).deriv

private def JcostDeriv' (x : ℝ) : ℝ := x ^ (-3 : ℤ)

private lemma hasDerivAt_JcostDeriv {x : ℝ} (hx : 0 < x) :
    HasDerivAt JcostDeriv (JcostDeriv' x) x := by
  have hxne : (x : ℝ) ≠ 0 := ne_of_gt hx
  have hpow : HasDerivAt (fun y : ℝ => y ^ (-2 : ℤ)) ((-2 : ℝ) * x ^ (-3 : ℤ)) x := by
    simpa using (hasDerivAt_zpow (-2 : ℤ) x (Or.inl hxne))
  have hneg : HasDerivAt (fun y : ℝ => -y ^ (-2 : ℤ)) (2 * x ^ (-3 : ℤ)) x := by
    simpa [two_mul, mul_comm, mul_left_comm, mul_assoc] using hpow.neg
  have haux : HasDerivAt JcostDeriv (2 * x ^ (-3 : ℤ) / 2) x := by
    have := (hneg.add_const 1).const_mul ((1 : ℝ) / 2)
    simpa [JcostDeriv, one_div, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using this
  have hxpow : 2 * x ^ (-3 : ℤ) / 2 = x ^ (-3 : ℤ) := by
    simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  simpa [JcostDeriv', hxpow] using haux

private lemma deriv_JcostDeriv {x : ℝ} (hx : 0 < x) :
    deriv JcostDeriv x = JcostDeriv' x := (hasDerivAt_JcostDeriv hx).deriv

private lemma JcostDeriv_strictMonoOn : StrictMonoOn JcostDeriv (Ioi (0 : ℝ)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi (0 : ℝ)) ?hcont ?hpos
  · refine
      ((continuousOn_const.sub ?_).const_mul ((1 : ℝ) / 2))
    have : ContinuousOn (fun x : ℝ => x⁻²) (Ioi (0 : ℝ)) := by
      have hinv : ContinuousOn (fun x : ℝ => x⁻¹) (Ioi (0 : ℝ)) := continuousOn_inv₀.mono ?_
      · exact hinv.pow 2
      · intro x hx; exact hx.ne'
    simpa [pow_two] using this
  · intro x hx
    have hxpos : 0 < x := hx
    have hxne : (x : ℝ) ≠ 0 := ne_of_gt hxpos
    have hder := deriv_JcostDeriv hxpos
    have hxpow : 0 < x ^ (-3 : ℤ) := by
      have hxpos' : 0 < x ^ (3 : ℕ) := pow_pos hxpos (3 : ℕ)
      have hxrepr : x ^ (-3 : ℤ) = (x ^ (3 : ℕ))⁻¹ := by
        simpa [zpow_neg, hxne] using (zpow_neg x (3 : ℕ))
      simpa [hxrepr] using inv_pos.mpr hxpos'
    simpa [hder, JcostDeriv'] using hxpow

/-- Strict convexity of `Jcost` on `(0, ∞)`. -/
theorem Jcost_strictConvexOn_pos : StrictConvexOn ℝ (Ioi (0 : ℝ)) Jcost := by
  refine
    (StrictMonoOn.strictConvexOn_of_deriv (convex_Ioi (0 : ℝ))
        ?hcont ?hmono)
  · refine
      ((continuousOn_const.sub ?_).const_mul ((1 : ℝ) / 2)).sub continuousOn_const
    have hinv : ContinuousOn (fun x : ℝ => x⁻¹) (Ioi (0 : ℝ)) := continuousOn_inv₀.mono ?_
    · simpa [pow_two] using hinv.pow 2
    · intro x hx; exact hx.ne'
  · have hmono := JcostDeriv_strictMonoOn
    refine hmono.congr ?h_eq
    intro x hx
    simpa [JcostDeriv] using deriv_Jcost hx

/-- Helper: Jcost on positive reals via composition with exp -/
lemma Jcost_as_composition {x : ℝ} (hx : 0 < x) :
  Jcost x = Jlog (log x) := by
  unfold Jlog Jcost
  rw [exp_log hx]
  have : x⁻¹ = exp (- log x) := by
    rw [exp_neg, exp_log hx]
  rw [this]

end Cost
end IndisputableMonolith
