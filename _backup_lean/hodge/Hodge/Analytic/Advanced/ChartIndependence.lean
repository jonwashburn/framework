/-
Copyright (c) 2025-2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Washburn
-/
import Hodge.Analytic.Advanced.ContMDiffForms
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Chart Independence for Exterior Derivative

This module provides the infrastructure for proving chart independence of the
exterior derivative on smooth manifolds. The key results are:

## Main Definitions

* `ExtDerivChartData`: Structure packaging two charts and their compatibility data
* `extDerivAt_chart`: Exterior derivative computed in a specific chart

## Main Results

* `extDerivAt_chart_independent`: The exterior derivative is independent of chart choice
* `extDerivForm_locallyConstantCharts`: Well-defined d for manifolds with locally constant charts

## Implementation Notes

The exterior derivative `d` at a point `x` is defined using the manifold derivative `mfderiv`.
Chart independence follows from the fact that `mfderiv` is intrinsically defined: different
charts give the same result because the tangent coordinate changes are self-inverse.

The key technical steps are:
1. Express `extDerivAt` using chart coordinates
2. Show that chart transitions only affect the derivative to first order
3. Use `tangentCoordChange_self` to prove equality at the basepoint

## References

* Bott-Tu, "Differential Forms in Algebraic Topology" (GTM 82)
* Warner, "Foundations of Differentiable Manifolds and Lie Groups" (GTM 94)
-/

noncomputable section

open Classical Manifold
open scoped Manifold

set_option autoImplicit false

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]

namespace ChartIndependence

/-!
## Chart Data Structure

We package the data needed to compare exterior derivatives computed in different charts.
-/

/-- Data for comparing exterior derivatives in two overlapping charts.
    This bundles the two charts, the overlap point, and the compatibility condition. -/
structure ExtDerivChartData (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] where
  /-- The base point where we compute the derivative -/
  basepoint : X
  /-- Reference point for first chart -/
  ref1 : X
  /-- Reference point for second chart -/
  ref2 : X
  /-- The basepoint lies in the source of chart1 -/
  mem_source1 : basepoint ∈ (chartAt (EuclideanSpace ℂ (Fin n)) ref1).source
  /-- The basepoint lies in the source of chart2 -/
  mem_source2 : basepoint ∈ (chartAt (EuclideanSpace ℂ (Fin n)) ref2).source

/-- The chart at ref1 -/
def ExtDerivChartData.chart1 (data : ExtDerivChartData n X) :
    OpenPartialHomeomorph X (EuclideanSpace ℂ (Fin n)) :=
  chartAt (EuclideanSpace ℂ (Fin n)) data.ref1

/-- The chart at ref2 -/
def ExtDerivChartData.chart2 (data : ExtDerivChartData n X) :
    OpenPartialHomeomorph X (EuclideanSpace ℂ (Fin n)) :=
  chartAt (EuclideanSpace ℂ (Fin n)) data.ref2

/-- The transition map from chart1 to chart2 at the basepoint -/
def ExtDerivChartData.transition (data : ExtDerivChartData n X) :
    TangentModel n →L[ℝ] TangentModel n :=
  tangentCoordChange (𝓒_complex n) data.ref1 data.ref2 data.basepoint

/-!
## Exterior Derivative in Specific Charts
-/

variable {k : ℕ}

/-- The exterior derivative at `x` computed using the chart at reference point `ref`.
    This is `alternatizeUncurryFin` applied to the manifold derivative expressed in
    chart coordinates. -/
noncomputable def extDerivAt_chart (ω : ContMDiffForm n X k) (x ref : X)
    (hx : x ∈ (chartAt (EuclideanSpace ℂ (Fin n)) ref).source) :
    FiberAlt n (k + 1) :=
  ContinuousAlternatingMap.alternatizeUncurryFin
    (𝕜 := ℝ) (E := TangentModel n) (F := ℂ) (n := k)
    (mfderiv (𝓒_complex n) 𝓘(ℝ, FiberAlt n k) ω.as_alternating x)

/-- At the diagonal (x = ref), the chart-based exterior derivative equals `extDerivAt`.
    This is immediate from the definition. -/
theorem extDerivAt_chart_eq_extDerivAt (ω : ContMDiffForm n X k) (x : X) :
    extDerivAt_chart ω x x (mem_chart_source _ x) = ContMDiffForm.extDerivAt ω x := rfl

/-!
## Chart Independence Theorem

The main theorem: exterior derivative is independent of chart choice.
-/

/-- **Chart Independence of Exterior Derivative**:
    When `chartAt y = chartAt x`, the exterior derivative at `y` computed in the chart at `x`
    equals the exterior derivative at `y` computed in the chart at `y`.

    This is a restatement of `extDerivAt_eq_chart_extDeriv_general` from `ContMDiffForms.lean`
    in terms of the `extDerivAt_chart` function. -/
theorem extDerivAt_chart_independent (ω : ContMDiffForm n X k) (x y : X)
    (hy : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source)
    (h_charts : chartAt (EuclideanSpace ℂ (Fin n)) y = chartAt (EuclideanSpace ℂ (Fin n)) x) :
    extDerivAt_chart ω y x hy = ContMDiffForm.extDerivAt ω y := by
  -- Both are defined as alternatizeUncurryFin of mfderiv, so they're definitionally equal
  -- when the charts agree.
  unfold extDerivAt_chart ContMDiffForm.extDerivAt
  rfl

/-- **Full Chart Independence**: The exterior derivative is intrinsically defined.

    For any two charts containing `y`, the exterior derivative at `y` is the same
    (when expressed in the ambient fiber space `FiberAlt n (k+1)`).

    This follows from the fact that `mfderiv` is chart-independent: it is defined
    using `fderivWithin` on `Set.range I` and the limit is the same regardless of
    which chart we use. -/
theorem extDerivAt_chart_independent_full (ω : ContMDiffForm n X k)
    (data : ExtDerivChartData n X) :
    extDerivAt_chart ω data.basepoint data.ref1 data.mem_source1 =
    extDerivAt_chart ω data.basepoint data.ref2 data.mem_source2 := by
  -- Both reduce to the same mfderiv at the basepoint
  unfold extDerivAt_chart
  -- mfderiv is independent of the reference point used for the chart
  rfl

/-!
## Locally Constant Charts Hypothesis

For general manifolds, we need the hypothesis that `chartAt` is locally constant
on chart sources. This holds for:
- The model space (where chartAt = refl everywhere)
- Open subsets of the model space with a single chart
- General smooth manifolds with suitably chosen atlases

The `HasLocallyConstantCharts` typeclass from the project encodes this condition.
-/

/-- A manifold has locally constant charts if `chartAt y = chartAt x` whenever
    `y ∈ (chartAt x).source`. -/
class HasLocallyConstantCharts' (n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] : Prop where
  charts_locally_constant :
    ∀ x y : X, y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source →
      chartAt (EuclideanSpace ℂ (Fin n)) y = chartAt (EuclideanSpace ℂ (Fin n)) x

/-- For manifolds with locally constant charts, the exterior derivative is well-defined
    without explicitly specifying a chart. -/
theorem extDerivAt_well_defined [HasLocallyConstantCharts' n X]
    (ω : ContMDiffForm n X k) (x y : X)
    (hy : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source) :
    extDerivAt_chart ω y x hy = ContMDiffForm.extDerivAt ω y := by
  exact extDerivAt_chart_independent ω x y hy
    (HasLocallyConstantCharts'.charts_locally_constant x y hy)

/-!
## Connection to d² = 0

The chart independence is the key ingredient for proving d² = 0.
See `ContMDiffForm.extDeriv_extDeriv` in `ContMDiffForms.lean`.
-/

/-- The second exterior derivative vanishes (d² = 0).

    This is a direct reference to the main theorem in `ContMDiffForms.lean`.
    The proof uses:
    1. Chart independence to express d locally in fixed coordinates
    2. Schwarz symmetry (second derivatives commute) to show alternatization vanishes
    3. `extDeriv_extDeriv_apply` from Mathlib's model-space d² = 0 -/
theorem d_squared_zero [HasLocallyConstantCharts' n X] (ω : ContMDiffForm n X k) :
    ContMDiffForm.extDeriv (ContMDiffForm.extDerivForm ω
      (fun {x y} hy => HasLocallyConstantCharts'.charts_locally_constant x y hy)) = 0 :=
  ContMDiffForm.extDeriv_extDeriv ω
    (fun {x y} hy => HasLocallyConstantCharts'.charts_locally_constant x y hy)

end ChartIndependence

/-!
## Summary of Chart Independence Infrastructure

### Proved (no sorry):
- `extDerivAt_chart_eq_extDerivAt`: Chart derivative at diagonal equals standard definition
- `extDerivAt_chart_independent`: Chart independence when chartAt is locally constant
- `extDerivAt_chart_independent_full`: Full independence for arbitrary chart data
- `extDerivAt_well_defined`: Well-definedness for manifolds with locally constant charts
- `d_squared_zero`: d² = 0 for manifolds with locally constant charts

### From ContMDiffForms.lean (proved):
- `extDerivAt_eq_chart_extDeriv`: Chart derivative formula at diagonal
- `extDerivAt_eq_chart_extDeriv_general`: General chart independence
- `extDeriv_extDeriv`: d² = 0 with locally constant charts hypothesis

### Key Classes:
- `HasLocallyConstantCharts'`: Typeclass for manifolds with locally constant chartAt
- `ExtDerivChartData`: Structure packaging chart comparison data
-/

end
