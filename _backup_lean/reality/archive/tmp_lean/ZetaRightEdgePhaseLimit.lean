import RiemannRecognitionGeometry.ExplicitFormula.ZetaInstantiation

/-!
# Route 3: ζ right-edge phase-limit scaffolding

This file contains **convenience constructors** for the end-to-end ζ run, focusing on the
`RightEdgePhaseLimitAssumptions` bundle.

No new analytic theorems are proved here; we just reduce boilerplate by noting that for
`PSCComponents_zeta` we have `P.xi = xiLagarias` definitionally.
-/

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula
namespace ZetaInstantiation

open MeasureTheory Complex

namespace EndToEnd

/-- Build a `LagariasContourFramework` with `xi := xiLagarias`. -/
def mkLagariasContourFramework_xiLagarias
    {F : Type} [TestSpace F]
    (L : LagariasFramework F)
    (c : ℝ)
    (contourW1 : ContourW1.W1LimitAssumptions (F := F) xiLagarias c)
    (W1_eq : L.W1 = contourW1.W1) :
    LagariasContourFramework F :=
  { L := L
    xi := xiLagarias
    c := c
    contourW1 := contourW1
    W1_eq := W1_eq }

/--
Build `RightEdgePhaseLimitAssumptions` for `PSCComponents_zeta`, given the three analytic limit facts.

`xiP` is discharged definitionally (`PSCComponents_zeta H).xi = xiLagarias`.
-/
def rightEdgePhaseLimitAssumptions_zeta
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (H : ZetaPSCHypotheses)
    (hxiLC : LC.xi = xiLagarias)
    (hBot :
      ∀ h : F,
        Filter.Tendsto
          (fun T : ℝ =>
            ContourW1.horizBottom (fun s : ℂ => M[h](s) * logDeriv LC.xi s) LC.c T)
          Filter.atTop (nhds 0))
    (hTop :
      ∀ h : F,
        Filter.Tendsto
          (fun T : ℝ =>
            ContourW1.horizTop (fun s : ℂ => M[h](s) * logDeriv LC.xi s) LC.c T)
          Filter.atTop (nhds 0))
    (hRight :
      ∀ h : F,
        Filter.Tendsto
          (fun T : ℝ =>
            ContourW1.vertRight (fun s : ℂ => M[h](s) * logDeriv LC.xi s) LC.c T +
              ContourW1.vertRight (fun s : ℂ => M[(TestSpace.tilde (F := F) h)](s) * logDeriv LC.xi s)
                LC.c T)
          Filter.atTop
          (nhds (Complex.I *
            ∫ t : ℝ,
              -(M[h](1/2 + Complex.I * t) *
                  ((deriv (ContourToBoundary.boundaryPhaseFunction (PSCComponents_zeta H)) t : ℝ) : ℂ))
                ∂ volume))) :
    ExplicitFormulaCancellationSkeleton.RightEdgePhaseLimitAssumptions
      (LC := LC) (P := PSCComponents_zeta H) :=
  { xiLC := hxiLC
    xiP := by
      -- `PSCComponents_zeta H).xi = xi_zeta = xiLagarias`.
      rfl
    horizBottom_vanish := hBot
    horizTop_vanish := hTop
    rightEdge_phase_limit := hRight }

/--
Build `RightEdgePhaseLimitAssumptions` for ζ from:
- horizontal-vanishing hypotheses, and
- the *integrability + full-line integral identity* bundle `RightEdgeIntegralIdentityAssumptions`.

This avoids having to restate the `Tendsto` target explicitly: it is derived via
`rightEdge_phase_limit_of_RightEdgeIntegralIdentityAssumptions`.
-/
def rightEdgePhaseLimitAssumptions_zeta_of_rightEdgeIntegralIdentityAssumptions
    {F : Type} [TestSpace F]
    (LC : LagariasContourFramework F)
    (H : ZetaPSCHypotheses)
    (hxiLC : LC.xi = xiLagarias)
    (hBot :
      ∀ h : F,
        Filter.Tendsto
          (fun T : ℝ =>
            ContourW1.horizBottom (fun s : ℂ => M[h](s) * logDeriv LC.xi s) LC.c T)
          Filter.atTop (nhds 0))
    (hTop :
      ∀ h : F,
        Filter.Tendsto
          (fun T : ℝ =>
            ContourW1.horizTop (fun s : ℂ => M[h](s) * logDeriv LC.xi s) LC.c T)
          Filter.atTop (nhds 0))
    (AId :
      ExplicitFormulaCancellationSkeleton.RightEdgeIntegralIdentityAssumptions
        (LC := LC) (P := PSCComponents_zeta H)) :
    ExplicitFormulaCancellationSkeleton.RightEdgePhaseLimitAssumptions
      (LC := LC) (P := PSCComponents_zeta H) :=
by
  refine rightEdgePhaseLimitAssumptions_zeta (LC := LC) (H := H) (hxiLC := hxiLC)
      (hBot := hBot) (hTop := hTop) (hRight := ?_)
  intro h
  -- Derive the `Tendsto` statement from integrability + full-line integral identity.
  have hRight' :
      Filter.Tendsto
        (fun T : ℝ =>
          ContourW1.vertRight (fun s : ℂ => M[h](s) * logDeriv LC.xi s) LC.c T +
            ContourW1.vertRight (fun s : ℂ =>
                M[(TestSpace.tilde (F := F) h)](s) * logDeriv LC.xi s) LC.c T)
        Filter.atTop
        (nhds (Complex.I *
          ∫ t : ℝ,
            ExplicitFormulaCancellationSkeleton.boundaryPhaseIntegrand (PSCComponents_zeta H) h t ∂ volume)) := by
    simpa using
      (ExplicitFormulaCancellationSkeleton.rightEdge_phase_limit_of_RightEdgeIntegralIdentityAssumptions
        (LC := LC) (P := PSCComponents_zeta H) (A := AId) (h := h))
  simpa [ExplicitFormulaCancellationSkeleton.boundaryPhaseIntegrand] using hRight'

end EndToEnd

end ZetaInstantiation
end ExplicitFormula
end RiemannRecognitionGeometry
