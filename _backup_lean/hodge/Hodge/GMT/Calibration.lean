/-
Copyright (c) 2024 Hodge Conjecture Formalization Project. All rights reserved.
Released under Apache 2.0 license.
-/
import Hodge.GMT.CalibratedGeometry

/-!
# GMT: Calibration (compatibility wrapper)

The proof-track calibration definitions and lemmas live in `Hodge/Analytic/Calibration.lean`
and are re-exported under the planned GMT module hierarchy in
`Hodge/GMT/CalibratedGeometry.lean`.

This module keeps the historical name `Hodge.GMT.Calibration` available as a thin import layer,
and provides a couple of legacy aliases.
-/

noncomputable section

open Classical

set_option autoImplicit false

namespace Hodge.GMT

variable {n : ℕ} {X : Type*}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]

/-! ## Legacy aliases -/

/-- Legacy name: a “calibration” is a calibrating form. Prefer `CalibratingForm`. -/
abbrev Calibration (k : ℕ) : Type _ :=
  CalibratingForm (n := n) (X := X) k

/-- Legacy name: calibrated current predicate. Prefer `isCalibrated`. -/
abbrev IsCalibratedCurrent {k : ℕ} (T : Current n X k) (φ : Calibration (n := n) (X := X) k) : Prop :=
  isCalibrated (n := n) (X := X) T φ

end Hodge.GMT
