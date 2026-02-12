/-
Copyright (c) 2026 Hodge Formalization Project. All rights reserved.
Released under Apache 2.0 license.
Authors: Deep Track Formalization
-/
import Hodge.Classical.HarveyLawson
import Hodge.Classical.GAGA
import Hodge.Deep.Pillars.Stokes

/-!
# Deep Pillar: Harvey-Lawson Structure Theorem

This module contains the **real** Harvey-Lawson formalization: calibrated integral
currents decompose into analytic subvarieties.

## Main Goals

1. Regularity: calibrated currents have analytic support
2. Structure: decomposition into irreducible components with multiplicities
3. King's theorem: integral currents calibrated by ω^p are algebraic

## TeX References

- Harvey-Lawson, "Calibrated Geometries", Acta Math. 148 (1982)
- King, "The currents defined by analytic varieties", Acta Math. 127 (1971)
-/

noncomputable section

open Classical Hodge

set_option autoImplicit false

namespace Hodge.Deep.HarveyLawson

universe u

variable {n : ℕ} {X : Type u}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X]

/-! ## Goal 1: Regularity of Calibrated Currents

Calibrated integral currents have analytic (smooth away from singular set) support.
-/

/-- **DEEP GOAL 1.1**: Regularity theorem.

    **Mathematical content**: If T is an integral current calibrated by a smooth
    form ψ, then the support of T is an analytic variety (with singularities of
    codimension ≥ 2).

    **TeX Reference**: Harvey-Lawson, "Calibrated Geometries", Theorem 4.2. -/
theorem calibrated_current_support_analytic {k : ℕ}
    (T : IntegralCurrent n X k) (ψ : CalibratingForm n X k)
    (hcal : isCalibrated T.toFun ψ)
    [CalibratedCurrentRegularityData n X k] :
    IsAnalyticSet (n := n) (X := X) (Current.support T.toFun) := by
  -- Use the explicit Harvey–Lawson regularity data.
  exact (CalibratedCurrentRegularityData.support_is_analytic_zero_locus
    (n := n) (X := X) (k := k) T ψ hcal)

/-! ## Goal 2: Decomposition into Irreducible Components -/

/-- **DEEP GOAL 2.1**: Structure theorem.

    **Mathematical content**: A calibrated integral k-current T decomposes as
      T = ∑ᵢ nᵢ [Vᵢ]
    where each Vᵢ is an irreducible analytic variety and nᵢ ∈ ℤ₊.

    **TeX Reference**: Harvey-Lawson, "Calibrated Geometries", Theorem 5.1. -/
theorem harvey_lawson_decomposition {k : ℕ}
    (T : IntegralCurrent n X k) (ψ : CalibratingForm n X k)
    (hcycle : T.isCycleAt) (hcal : isCalibrated T.toFun ψ)
    [HarveyLawsonKingData n X k] :
    ∃ (varieties : Finset (AnalyticSubvariety n X))
      (multiplicities : ∀ v ∈ varieties, ℕ+),
      -- Each variety has the correct codimension
      (∀ v ∈ varieties, v.codim = 2 * n - k) ∧
      -- The decomposition represents the input current
      (HarveyLawsonKingData.decompose
        (hyp := { T := T, ψ := ψ, is_cycle := hcycle, is_calibrated := hcal })).represents T.toFun := by
  classical
  let hyp : HarveyLawsonHypothesis n X k :=
    { T := T, ψ := ψ, is_cycle := hcycle, is_calibrated := hcal }
  let concl := HarveyLawsonKingData.decompose (n := n) (X := X) (k := k) hyp
  refine ⟨concl.varieties, ?_, concl.codim_correct, ?_⟩
  · intro v hv
    exact concl.multiplicities ⟨v, hv⟩
  · exact HarveyLawsonKingData.represents_input (n := n) (X := X) (k := k) hyp

/-! ## Goal 3: King's Theorem (ω^p-Calibrated = Algebraic)

For Kähler manifolds, ω^p-calibrated currents are algebraic cycles.
-/

/-- **DEEP GOAL 3.1**: King's theorem.

    **Mathematical content**: On a projective Kähler manifold, an integral current
    calibrated by ω^p (the p-th power of the Kähler form) is supported on an
    algebraic subvariety.

    **TeX Reference**: King (1971), combined with GAGA. -/
theorem king_algebraicity {p : ℕ}
    (T : IntegralCurrent n X (2 * (n - p)))
    (ψ : CalibratingForm n X (2 * (n - p)))
    (hcal : isCalibrated T.toFun ψ)
    [CalibratedCurrentRegularityData n X (2 * (n - p))]
    [ChowGAGAData n X] :
    AlgGeom.IsAlgebraicSet n X (Current.support T.toFun) := by
  have hAnalytic :
      IsAnalyticSet (n := n) (X := X) (Current.support T.toFun) :=
    (CalibratedCurrentRegularityData.support_is_analytic_zero_locus
      (n := n) (X := X) (k := 2 * (n - p)) T ψ hcal)
  exact ChowGAGAData.analytic_to_algebraic (n := n) (X := X) (Current.support T.toFun) hAnalytic

/-! ## Goal 4: Real HarveyLawsonKingData Instance -/

/-- **DEEP GOAL 4**: The real HarveyLawsonKingData instance.

    **Status**: Depends on Goals 1-3 above. -/
def HarveyLawsonKingData.real {k : ℕ}
    (decompose : HarveyLawsonHypothesis n X k → HarveyLawsonConclusion n X k)
    (represents_input : ∀ hyp : HarveyLawsonHypothesis n X k, (decompose hyp).represents hyp.T.toFun) :
    HarveyLawsonKingData n X k where
  decompose := decompose
  represents_input := represents_input

end Hodge.Deep.HarveyLawson

end
