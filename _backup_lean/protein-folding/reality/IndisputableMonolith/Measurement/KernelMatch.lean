import Mathlib
import IndisputableMonolith.Cost.JcostCore
import IndisputableMonolith.Cost.Jlog
import IndisputableMonolith.Measurement.PathAction
import IndisputableMonolith.Measurement.TwoBranchGeodesic

/-!
# Kernel Matching: Pointwise Identity J(r) dt = 2 dA

This module proves the constructive kernel match from Local-Collapse Appendix D.

The key lemma: for the profile r(ϑ) = exp(arcosh(1 + 2 tan ϑ)),
we have J(r(ϑ)) = 2 tan ϑ pointwise, enabling the integral identity C = 2A.
-/

namespace IndisputableMonolith
namespace Measurement

open Real Cost

-- Use Real.arcosh from Mathlib

/-- Recognition profile from eq (D.1) of Local-Collapse:
    u(ϑ) = arcosh(1 + 2 tan ϑ), r(ϑ) = exp(u(ϑ)) -/
noncomputable def recognitionProfile (ϑ : ℝ) : ℝ :=
  Real.exp (Real.arcosh (1 + 2 * Real.tan ϑ))

/-- The argument to arcosh is at least 1 for ϑ ∈ [0, π/2) -/
lemma arcosh_arg_ge_one (ϑ : ℝ) (hϑ : 0 ≤ ϑ ∧ ϑ < π/2) :
  1 ≤ 1 + 2 * Real.tan ϑ := by
  have : 0 ≤ Real.tan ϑ := by
    apply tan_nonneg_of_nonneg_of_le_pi_div_two hϑ.1
    exact hϑ.2.le
  linarith

/-- Recognition profile is positive -/
lemma recognitionProfile_pos (ϑ : ℝ) (hϑ : 0 ≤ ϑ ∧ ϑ < π/2) :
  0 < recognitionProfile ϑ := by
  unfold recognitionProfile
  exact Real.exp_pos _

/-- Pointwise kernel matching: J(r(ϑ)) = 2 tan ϑ
    This is the core technical lemma enabling C = 2A -/
theorem kernel_match_pointwise (ϑ : ℝ) (hϑ : 0 ≤ ϑ ∧ ϑ < π/2) :
  Jcost (recognitionProfile ϑ) = 2 * Real.tan ϑ := by
  unfold recognitionProfile Jcost
  have hy : 1 ≤ 1 + 2 * Real.tan ϑ := arcosh_arg_ge_one ϑ hϑ
  -- Jcost(exp u) = (exp u + exp(-u))/2 - 1 = cosh u - 1
  -- where u = arcosh(1 + 2 tan ϑ)
  -- By definition: cosh(arcosh(y)) = y for y ≥ 1
  have : (exp (Real.arcosh (1 + 2 * tan ϑ)) + exp (-(Real.arcosh (1 + 2 * tan ϑ)))) / 2 - 1
       = (1 + 2 * tan ϑ) - 1 := by
    have hcosh : cosh (Real.arcosh (1 + 2 * tan ϑ)) = 1 + 2 * tan ϑ := Real.cosh_arcosh hy
    unfold cosh at hcosh
    convert hcosh using 1
    ring
  convert this using 2
  ring

/-- Differential form of kernel match: J(r) dϑ = 2 tan ϑ dϑ -/
theorem kernel_match_differential (ϑ : ℝ) (hϑ : 0 ≤ ϑ ∧ ϑ < π/2) :
  Jcost (recognitionProfile ϑ) = 2 * Real.tan ϑ :=
  kernel_match_pointwise ϑ hϑ

/-- The integrand match: ∫ J(r(ϑ)) dϑ = 2 ∫ tan ϑ dϑ -/
theorem kernel_integral_match (θ_s : ℝ) (hθ : 0 < θ_s ∧ θ_s < π/2) :
  ∫ ϑ in (0)..(π/2 - θ_s), Jcost (recognitionProfile (ϑ + θ_s)) =
  2 * ∫ ϑ in (0)..(π/2 - θ_s), Real.tan (ϑ + θ_s) := by
  -- Follows by integrating the pointwise identity
  -- measurability and integrability are standard for these smooth functions
  have hpt : ∀ ϑ ∈ Set.Icc (0 : ℝ) (π/2 - θ_s),
      Jcost (recognitionProfile (ϑ + θ_s)) = 2 * Real.tan (ϑ + θ_s) := by
    intro ϑ hϑ
    apply kernel_match_pointwise (ϑ + θ_s)
    constructor
    · have : 0 ≤ ϑ := hϑ.1
      exact this.trans (le_of_lt hθ.1)
    · have : ϑ ≤ π/2 - θ_s := hϑ.2
      linarith
  have := intervalIntegral.integral_congr_ae (a := 0) (b := π/2 - θ_s) (f := fun ϑ => Jcost (recognitionProfile (ϑ + θ_s))) (g := fun ϑ => 2 * Real.tan (ϑ + θ_s))
  -- build an AE equality from pointwise on Icc
  have h_ae : (Filter.ae (MeasureTheory.Measure.restrict MeasureTheory.Measure.real (Set.Icc 0 (π/2 - θ_s))) fun ϑ => Jcost (recognitionProfile (ϑ + θ_s)) = 2 * Real.tan (ϑ + θ_s)) := by
    refine Filter.eventually_of_forall ?h
    intro ϑ
    intro hϑ
    exact hpt ϑ hϑ
  have hcongr := this h_ae
  simpa using hcongr

end Measurement
end IndisputableMonolith
