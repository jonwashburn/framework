/-
Copyright (c) 2024 Hodge Conjecture Formalization Project. All rights reserved.
Released under Apache 2.0 license.
-/
import Hodge.Analytic.Currents
import Hodge.Analytic.Norms
import Hodge.Analytic.FlatNorm

/-!
# GMT: Mass / Comass (wrapper)

The project’s *real* comass and mass live in:
- `Hodge/Analytic/Norms.lean`  (`_root_.comass` on `SmoothForm`)
- `Hodge/Analytic/Currents.lean` (`Current.mass` on `Current`)

Historically, this repository also contained an older “test-form as `Unit`” GMT stub with an
`opaque` comass and ENNReal-valued `mass`. That regime is no longer used by the proof track nor
the `Hodge.GMT` umbrella; it made automation look successful while hiding mathematical content.

This file is therefore a **thin re-export** matching the planned module location
`Hodge.GMT.Mass`, while delegating to the analytic implementation.
-/

noncomputable section

open Classical

set_option autoImplicit false

namespace Hodge.GMT

variable {n : ℕ} {X : Type*} {k : ℕ}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]
  [Nonempty X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-! ## Re-exports -/

/-- Comass norm on smooth forms (re-export of `_root_.comass`). -/
abbrev comass (ω : SmoothForm n X k) : ℝ :=
  _root_.comass ω

/-- Mass of a current (re-export of `Current.mass`). -/
abbrev mass (T : Current n X k) : ℝ :=
  Current.mass T

/-- Basic inequality: evaluation is bounded by mass × comass (re-export). -/
abbrev eval_le_mass (T : Current n X k) (ψ : SmoothForm n X k) :
    |T.toFun ψ| ≤ mass (n := n) (X := X) (k := k) T * comass (n := n) (X := X) (k := k) ψ :=
  _root_.eval_le_mass (n := n) (X := X) (k := k) T ψ

end Hodge.GMT
