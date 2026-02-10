import RiemannRecognitionGeometry.ExplicitFormula.ZetaInstantiation
import RiemannRecognitionGeometry.ExplicitFormula.PSCSplice
import RiemannRecognitionGeometry.ExplicitFormula.ZetaRightEdgePhaseLimit

/-!
# Route 3: end-to-end ζ run (Route 3 test space)

This file is a wiring/sanity target:

Given
- a concrete `LagariasContourFramework` on Route‑3’s fixed test space `Route3.F`,
- ζ PSC-components (`PSCComponents_zeta`), and
- the remaining contour-to-boundary analytic hypotheses packaged as
  `RightEdgePhaseLimitAssumptions`,

we can fire the existing Route‑3 pipeline and obtain `RiemannHypothesis`.

No new analytic theorems are proved here; everything is assumptions → wiring.
-/

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula
namespace ZetaInstantiation

open MeasureTheory Complex

namespace EndToEnd

/-!
## End-to-end: `RightEdgePhaseLimitAssumptions` → RH
-/

variable [TestSpace Route3.F]

/-- All remaining hypotheses needed to run the ζ chain to `RiemannHypothesis` on `Route3.F`. -/
structure Assumptions where
  LC : LagariasContourFramework Route3.F
  H : ZetaPSCHypotheses
  Aphase :
    ExplicitFormulaCancellationSkeleton.RightEdgePhaseLimitAssumptions
      (LC := LC) (P := (PSCComponents_zeta H))
  transform : Route3.F →ₗ[ℂ] (ℝ → ℂ)
  transform_eq_mellinOnCriticalLine :
    ∀ f : Route3.F,
      transform f = fun t : ℝ => mellinOnCriticalLine (F := Route3.F) f t
  memL2 : ∀ f : Route3.F, MeasureTheory.Memℒp (transform f) 2 (PSCComponents_zeta H).μ_spec
  integrable_pairTransform_volume :
    ∀ f g : Route3.F,
      Integrable
        (fun t : ℝ => (starRingEnd ℂ (transform f t)) * (transform g t))
        volume
  integrable_pairTransform_deriv_volume :
    ∀ f g : Route3.F,
      Integrable
        (fun t : ℝ =>
          ((starRingEnd ℂ (transform f t)) * (transform g t)) *
            ((deriv (ContourToBoundary.boundaryPhaseFunction (PSCComponents_zeta H)) t : ℝ) : ℂ))
        volume
  integrable_pairTransform_μ :
    ∀ f g : Route3.F,
      Integrable
        (fun t : ℝ => (starRingEnd ℂ (transform f t)) * (transform g t))
        (PSCComponents_zeta H).μ_spec

theorem RH (A : Assumptions) : RiemannHypothesis := by
  classical

  -- 1) Get `explicit_formula_cancellation_contour` for all `h` from the right-edge limit bundle.
  have hContour :
      ∀ h : Route3.F,
        ContourToBoundary.explicit_formula_cancellation_contour
          (LC := A.LC) (P := PSCComponents_zeta A.H) h := by
    intro h
    exact
      ExplicitFormulaCancellationSkeleton.explicit_formula_cancellation_contour_of_rightEdgePhaseLimitAssumptions
        (LC := A.LC) (P := PSCComponents_zeta A.H) A.Aphase h

  -- 2) Convert contour cancellation into the `explicit_formula_cancellation` hypothesis PSCSplice expects.
  have hExplicit :
      ∀ f g : Route3.F,
        ContourToBoundary.explicit_formula_cancellation
          (L := A.LC.L) (P := PSCComponents_zeta A.H) (h := pair (F := Route3.F) f g) := by
    intro f g
    exact
      ContourToBoundary.explicit_formula_cancellation_of_contour
        (LC := A.LC) (P := PSCComponents_zeta A.H) (h := pair (F := Route3.F) f g)
        (hContour (pair (F := Route3.F) f g))

  -- 3) Fire the Route‑3 pipeline.
  exact
    Route3.PSCSplice.RH_ofContourToBoundary
      (P := PSCComponents_zeta A.H)
      (L := A.LC.L)
      (transform := A.transform)
      (transform_eq_mellinOnCriticalLine := A.transform_eq_mellinOnCriticalLine)
      (memL2 := A.memL2)
      (h_explicit := hExplicit)
      (h_integrable_F := A.integrable_pairTransform_volume)
      (h_integrable_vol := A.integrable_pairTransform_deriv_volume)
      (h_integrable_μ := A.integrable_pairTransform_μ)

/--
Variant assumptions where the right-edge input is provided in the more structural form:

- horizontal vanishing (`horizBottom_vanish`, `horizTop_vanish`),
- plus `RightEdgeIntegralIdentityAssumptions` (integrability + full-line integral identity),

from which `RightEdgePhaseLimitAssumptions` is derived automatically.
-/
structure AssumptionsIntegralId where
  LC : LagariasContourFramework Route3.F
  H : ZetaPSCHypotheses
  /-- Identify the contour framework xi with `xiLagarias`. -/
  xiLC : LC.xi = xiLagarias
  /-- Horizontal edges vanish (all test functions). -/
  horizBottom_vanish :
    ∀ h : Route3.F,
      Filter.Tendsto
        (fun T : ℝ =>
          ContourW1.horizBottom (fun s : ℂ => M[h](s) * logDeriv LC.xi s) LC.c T)
        Filter.atTop (nhds 0)
  horizTop_vanish :
    ∀ h : Route3.F,
      Filter.Tendsto
        (fun T : ℝ =>
          ContourW1.horizTop (fun s : ℂ => M[h](s) * logDeriv LC.xi s) LC.c T)
        Filter.atTop (nhds 0)
  /-- Integrability + full-line integral identity (the key remaining analytic content). -/
  rightEdgeIntegralId :
    ExplicitFormulaCancellationSkeleton.RightEdgeIntegralIdentityAssumptions
      (LC := LC) (P := PSCComponents_zeta H)

  transform : Route3.F →ₗ[ℂ] (ℝ → ℂ)
  transform_eq_mellinOnCriticalLine :
    ∀ f : Route3.F,
      transform f = fun t : ℝ => mellinOnCriticalLine (F := Route3.F) f t
  memL2 : ∀ f : Route3.F, MeasureTheory.Memℒp (transform f) 2 (PSCComponents_zeta H).μ_spec
  integrable_pairTransform_volume :
    ∀ f g : Route3.F,
      Integrable
        (fun t : ℝ => (starRingEnd ℂ (transform f t)) * (transform g t))
        volume
  integrable_pairTransform_deriv_volume :
    ∀ f g : Route3.F,
      Integrable
        (fun t : ℝ =>
          ((starRingEnd ℂ (transform f t)) * (transform g t)) *
            ((deriv (ContourToBoundary.boundaryPhaseFunction (PSCComponents_zeta H)) t : ℝ) : ℂ))
        volume
  integrable_pairTransform_μ :
    ∀ f g : Route3.F,
      Integrable
        (fun t : ℝ => (starRingEnd ℂ (transform f t)) * (transform g t))
        (PSCComponents_zeta H).μ_spec

def AssumptionsIntegralId.toAssumptions (A : AssumptionsIntegralId) : Assumptions where
  LC := A.LC
  H := A.H
  Aphase :=
    ZetaInstantiation.EndToEnd.rightEdgePhaseLimitAssumptions_zeta_of_rightEdgeIntegralIdentityAssumptions
      (LC := A.LC) (H := A.H)
      (hxiLC := A.xiLC)
      (hBot := A.horizBottom_vanish)
      (hTop := A.horizTop_vanish)
      (AId := A.rightEdgeIntegralId)
  transform := A.transform
  transform_eq_mellinOnCriticalLine := A.transform_eq_mellinOnCriticalLine
  memL2 := A.memL2
  integrable_pairTransform_volume := A.integrable_pairTransform_volume
  integrable_pairTransform_deriv_volume := A.integrable_pairTransform_deriv_volume
  integrable_pairTransform_μ := A.integrable_pairTransform_μ

theorem RH_of_integralId (A : AssumptionsIntegralId) : RiemannHypothesis :=
  RH (A := A.toAssumptions)

end EndToEnd

end ZetaInstantiation
end ExplicitFormula
end RiemannRecognitionGeometry
