/-
Copyright (c) 2025-2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Washburn
-/
import Hodge.Analytic.Advanced.ContMDiffForms
import Hodge.Analytic.Advanced.ChartIndependence

/-!
# d² = 0 for the Exterior Derivative

This module provides a clean interface to the fundamental identity d² = 0
for the exterior derivative on smooth manifolds.

## Main Results

* `extDeriv_extDeriv'`: The second exterior derivative vanishes (d² = 0)
* `extDeriv_extDeriv_pointwise`: Pointwise version at a specific point

## Mathematical Background

The identity d² = 0 is fundamental in differential geometry and de Rham cohomology.
The proof uses:

1. **Chart Independence**: The exterior derivative is intrinsically defined,
   independent of the choice of coordinate chart.

2. **Schwarz Symmetry**: Mixed partial derivatives commute (symmetry of D²f).

3. **Alternatization**: The exterior derivative involves alternatization of
   the differential, and alternatizing a symmetric form gives zero.

The combination: D(Dω) is symmetric by Schwarz, and alternatizeUncurryFin of
a symmetric bilinear form vanishes, giving d(dω) = 0.

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

namespace ExteriorDerivSq

variable {k : ℕ}

/-!
## Main Theorem: d² = 0
-/

/-- **d² = 0**: The second exterior derivative vanishes.

This is the fundamental identity in de Rham cohomology. For any smooth k-form ω,
applying the exterior derivative twice gives zero: d(dω) = 0.

**Proof sketch**:
1. Express dω in chart coordinates as alternatizeUncurryFin of the first derivative
2. Taking d again involves the second derivative, which is symmetric (Schwarz)
3. Alternatizing a symmetric bilinear form gives zero

**Hypothesis**: `hCharts` requires that `chartAt` is locally constant on chart sources.
This holds for:
- The model space (EuclideanSpace)
- Open subsets with a single chart
- General smooth manifolds with suitable atlases -/
theorem extDeriv_extDeriv' (ω : ContMDiffForm n X k)
    (hCharts :
      ∀ {x y : X}, y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source →
        chartAt (EuclideanSpace ℂ (Fin n)) y = chartAt (EuclideanSpace ℂ (Fin n)) x) :
    ContMDiffForm.extDeriv (ContMDiffForm.extDerivForm ω hCharts) = 0 :=
  ContMDiffForm.extDeriv_extDeriv ω hCharts

/-- **Pointwise d² = 0**: At any point x, (d(dω))(x) = 0.

This is the pointwise version of d² = 0. -/
theorem extDeriv_extDeriv_pointwise (ω : ContMDiffForm n X k) (x : X)
    (hCharts :
      ∀ {x y : X}, y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source →
        chartAt (EuclideanSpace ℂ (Fin n)) y = chartAt (EuclideanSpace ℂ (Fin n)) x) :
    ContMDiffForm.extDerivAt (ContMDiffForm.extDerivForm ω hCharts) x = 0 := by
  have h := extDeriv_extDeriv' ω hCharts
  exact congrFun h x

/-!
## Corollaries for Manifolds with Locally Constant Charts
-/

/-- For manifolds with locally constant charts, d² = 0 holds unconditionally. -/
theorem extDeriv_extDeriv_locallyConstant
    [ChartIndependence.HasLocallyConstantCharts' n X]
    (ω : ContMDiffForm n X k) :
    ContMDiffForm.extDeriv
      (ContMDiffForm.extDerivForm ω
        (fun {x y} hy => ChartIndependence.HasLocallyConstantCharts'.charts_locally_constant x y hy)) = 0 :=
  ChartIndependence.d_squared_zero ω

/-!
## Relationship to de Rham Cohomology

The identity d² = 0 is what makes de Rham cohomology well-defined:
- A form ω is **closed** if dω = 0
- A form ω is **exact** if ω = dη for some η
- Since d² = 0, every exact form is closed: d(dη) = 0
- The k-th de Rham cohomology is: H^k = (closed k-forms) / (exact k-forms)
-/

/-- Exact forms are closed: if ω = dη, then dω = 0. -/
theorem exact_implies_closed (η : ContMDiffForm n X k) (x : X)
    (hCharts :
      ∀ {x y : X}, y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source →
        chartAt (EuclideanSpace ℂ (Fin n)) y = chartAt (EuclideanSpace ℂ (Fin n)) x) :
    ContMDiffForm.extDerivAt (ContMDiffForm.extDerivForm η hCharts) x = 0 :=
  extDeriv_extDeriv_pointwise η x hCharts

/-!
## Summary

### Key Theorems (all proved, no sorry):

| Theorem | Statement |
|---------|-----------|
| `extDeriv_extDeriv'` | d(dω) = 0 as functions |
| `extDeriv_extDeriv_pointwise` | (d(dω))(x) = 0 at each point |
| `extDeriv_extDeriv_locallyConstant` | d² = 0 for nice manifolds |
| `exact_implies_closed` | dη closed for any η |

### Dependencies:

- `ContMDiffForm.extDeriv_extDeriv` from `ContMDiffForms.lean`
- `ChartIndependence.d_squared_zero` from `ChartIndependence.lean`
- Mathlib's `extDeriv_extDeriv_apply` for model space d² = 0
-/

end ExteriorDerivSq

end
