/-
Copyright (c) 2026 Hodge Formalization Project. All rights reserved.
Released under Apache 2.0 license.
Authors: Deep Track Formalization
-/
import Hodge.Analytic.Currents
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Deep Pillar: Stokes / Integration (data-based, no semantic stubs)

This file used to contain a Set-based “Stokes pillar” with **semantic stubs**:

- `μH = 0` (fake Hausdorff measure);
- `formEvalAtPoint = 0` (fake form evaluation);
- `SubmanifoldIntegration.real.integral = 0` (fake integration theory).

Those are explicitly forbidden by the “no gotchas” spec.

The proof-track integration story has since migrated to **structured geometric objects**
carrying the right data:

- `OrientedRectifiableSetData` / `hausdorffIntegrate` for rectifiable integration currents;
- `ClosedSubmanifoldData` for the boundaryless case (Stokes term vanishes).

This module now serves as a small wrapper/re-export around the real integration code in
`Hodge/Analytic/Currents.lean`.
-/

noncomputable section

open Classical MeasureTheory Hodge

set_option autoImplicit false

namespace Hodge.Deep.Stokes

universe u

open Classical MeasureTheory Hodge
open scoped Manifold

variable {n : ℕ} {X : Type u}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X]

/-!
## Hausdorff measure

Mathlib provides the `d`-dimensional Hausdorff measure as `MeasureTheory.Measure.hausdorffMeasure d`
with notation `μH[d]` (scoped in `MeasureTheory`).
-/

/-- Convenience abbreviation for Hausdorff measure (same as `μH[d]`). -/
abbrev μH (d : ℝ) : Measure X := MeasureTheory.Measure.hausdorffMeasure (X := X) d

/-!
## Integration over structured objects

The repository’s “current” integration layer is the data-based notion
`OrientedRectifiableSetData` together with `hausdorffIntegrate`.
We re-export the two core analytic facts needed throughout the spine:
linearity and mass–comass boundedness.
-/

theorem hausdorffIntegrate_linear' {k : ℕ}
    (data : OrientedRectifiableSetData n X k) (c : ℝ) (ω₁ ω₂ : SmoothForm n X k) :
    hausdorffIntegrate data (c • ω₁ + ω₂) =
      c * hausdorffIntegrate data ω₁ + hausdorffIntegrate data ω₂ :=
  hausdorffIntegrate_linear (data := data) c ω₁ ω₂

theorem hausdorffIntegrate_bound' {k : ℕ}
    (data : OrientedRectifiableSetData n X k) (ω : SmoothForm n X k) :
    |hausdorffIntegrate data ω| ≤ data.mass * comass ω :=
  hausdorffIntegrate_bound (data := data) ω

/-!
## Stokes for closed submanifolds

For a closed (boundaryless) submanifold, Stokes reduces to the vanishing of the exact-form integral.
In the current modeling, this is recorded as data on `ClosedSubmanifoldData`.
-/

theorem ClosedSubmanifoldData.stokes_integral_exact_zero_succ {k' : ℕ}
    (data : ClosedSubmanifoldData n X (k' + 1)) (ω : SmoothForm n X k') :
    (∫ x in data.carrier,
        formVectorPairing (smoothExtDeriv ω) data.orientation x ∂data.measure).re = 0 := by
  simpa using (data.stokes_integral_exact_zero ω)

/-!
### Note on the legacy Set-based `SubmanifoldIntegration`

We intentionally do **not** provide a `SubmanifoldIntegration.real` instance here.
The Set-based interface in `Hodge/Analytic/Integration/HausdorffMeasure.lean` is now a
thin wrapper over explicit `SubmanifoldIntegrationData`, and will be retired in favor of
structured integration data (`OrientedRectifiableSetData` / `ClosedSubmanifoldData`).
-/

end Hodge.Deep.Stokes

end
