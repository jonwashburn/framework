import Hodge.Analytic.FlatNorm

/-!
# GMT: Flat Norm Topology (wrapper)

The flat norm is already defined and developed in `Hodge.Analytic.FlatNorm`.
This file re-exports it under the `Hodge.GMT` module hierarchy referenced in the
operational plan.
-/

noncomputable section

open Classical

set_option autoImplicit false

namespace Hodge.GMT

/-- Flat norm on currents, real-valued (re-export of `_root_.flatNorm`). -/
abbrev flatNormReal {n : ℕ} {X : Type*} {k : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X] [CompactSpace X]
    (T : Current n X k) : ℝ :=
  _root_.flatNorm T

/-- Flat norm on currents, packaged as an extended nonnegative real `ENNReal` (a.k.a. `ℝ≥0∞`). -/
def flatNorm {n : ℕ} {X : Type*} {k : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X] [CompactSpace X]
    (T : Current n X k) : ENNReal :=
  ENNReal.ofReal (flatNormReal T)

end Hodge.GMT
