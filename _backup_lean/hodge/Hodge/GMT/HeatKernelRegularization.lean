import Hodge.GMT.CurrentToForm
import Hodge.Analytic.Currents

/-!
# Heat Kernel Regularization (Scaffolding)

This module will host the **concrete regularization** of currents to smooth forms
via a heat‑kernel or mollifier construction on charts.

It is intentionally **scaffolding‑only** right now: we provide explicit interfaces
and a checklist of lemmas to implement, without introducing any stubs or axioms.

## Implementation Checklist

1. Define a heat‑kernel / mollifier on local charts.
2. Prove chart‑change compatibility (gluing to a global smoothing operator).
3. Show `regularize` maps currents to smooth forms.
4. Show `regularize` respects degrees and supports.
5. Show `regularize` commutes with `d` on cycles.
6. Provide quantitative bounds (mass → C^k bounds) as needed.

These steps should culminate in a concrete instance of
`Hodge.GMT.CurrentRegularizationData`.
-/

noncomputable section

open Classical

set_option autoImplicit false

namespace Hodge.GMT

/-- Parameters for heat‑kernel regularization (time parameter). -/
structure HeatKernelParams where
  time : ℝ
  time_pos : 0 < time

/-- **Heat‑kernel regularization data**.

This is a refinement of `CurrentRegularizationData` that records a smoothing
parameter. It carries **no** implementation by itself. -/
class HeatKernelRegularizationData (n : ℕ) (X : Type*) (k : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X]
    extends CurrentRegularizationData n X k where
  params : HeatKernelParams

/-- Build heat‑kernel regularization data from an explicit regularization operator
and a choice of heat‑kernel parameters. -/
noncomputable def heatKernelRegularizationData_of {n : ℕ} {X : Type*} {k : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X]
    (params : HeatKernelParams)
    (regularize : Current n X k → SmoothForm n X k) :
    HeatKernelRegularizationData n X k :=
  { regularize := regularize
    params := params }

/-- Regularize a current using the heat‑kernel interface. -/
noncomputable def heatKernelRegularize {n : ℕ} {X : Type*} {k : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X]
    [HeatKernelRegularizationData n X k]
    (T : Current n X k) : SmoothForm n X k :=
  regularizeCurrentToForm T

end Hodge.GMT
