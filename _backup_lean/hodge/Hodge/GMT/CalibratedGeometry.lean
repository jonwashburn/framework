import Hodge.Analytic.Calibration

/-!
# GMT: Calibrated Geometry (wrapper)

The operational plan assigns Agent 5 ownership of “calibration theory” under the GMT
namespace. This repository already implements the basic calibration definitions and
lemmas in `Hodge/Analytic/Calibration.lean`.

This file provides the planned module location `Hodge/GMT/CalibratedGeometry.lean` by
re-exporting those definitions under `Hodge.GMT`, avoiding duplicate parallel APIs.
-/

noncomputable section

open Classical

set_option autoImplicit false

namespace Hodge.GMT

variable {n : ℕ} {X : Type*}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
  [MeasurableSpace X] [BorelSpace X]

abbrev CalibratingForm (k : ℕ) : Type _ :=
  _root_.CalibratingForm n X k

abbrev KählerCalibration (p : ℕ) : CalibratingForm (n := n) (X := X) (2 * p) :=
  _root_.KählerCalibration (n := n) (X := X) p

abbrev isCalibrated {k : ℕ} (T : Current n X k) (ψ : CalibratingForm (n := n) (X := X) k) : Prop :=
  _root_.isCalibrated T ψ

abbrev calibrationDefect {k : ℕ} (T : Current n X k) (ψ : CalibratingForm (n := n) (X := X) k) : ℝ :=
  _root_.calibrationDefect T ψ

end Hodge.GMT
