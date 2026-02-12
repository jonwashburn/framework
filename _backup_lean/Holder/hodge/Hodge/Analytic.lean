import Hodge.Analytic.Forms
import Hodge.Analytic.Norms
import Hodge.Analytic.Currents
import Hodge.Analytic.IntegralCurrents
import Hodge.Analytic.Calibration
import Hodge.Analytic.Grassmannian
import Hodge.Analytic.FlatNorm

/-!
# Track B: Analytic/GMT Core

This module exports all the analytic machinery for currents, calibrations,
and geometric measure theory needed for the Hodge Conjecture proof.

## Integration Infrastructure
- `Hodge.Analytic.Integration.VolumeForm`: Kähler volume form ω^n/n!
- `Hodge.Analytic.Integration.TopFormIntegral`: Integration of top forms

## Archived (Off-Track)

The following modules were moved to `archive/Hodge/Analytic/` because they are
NOT used by the main theorem `hodge_conjecture'`:

- `Hodge.Analytic.Laplacian/`: Codifferential δ, Hodge Laplacian Δ
- `Hodge.Analytic.HodgeLaplacian`: Top-level Laplacian aggregator
- `Hodge.Analytic.HarmonicForms`: Harmonic form definitions

These represent work towards a complete Kähler geometry library but are not
required for the current proof architecture.
-/
