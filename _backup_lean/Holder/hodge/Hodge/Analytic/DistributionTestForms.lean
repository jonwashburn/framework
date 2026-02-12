import Hodge.Basic

import Mathlib.Analysis.Distribution.TestFunction

/-!
# Stage 1 (planned): Test forms via Mathlib's LF-space of test functions (Euclidean model)

This file is part of the long-term plan in `tex/archive/HodgePlan-mc-28.1.26.rtf`.

Mathlib already implements the canonical LF topology on compactly supported smooth functions on
open subsets of a **finite-dimensional normed space**:

- `Mathlib.Analysis.Distribution.TestFunction` defines `𝓓(Ω, F)` for an open set `Ω ⊆ E`
  (with `E` a real normed space) and a normed space `F`, and equips it with the LF topology.

This module records the specializations relevant for *Euclidean-model* differential forms:

- The “fiber” of k-forms is `FiberAlt n k` (continuous alternating maps on the tangent model).
- A Euclidean k-form with compact support can be represented as a test function
  `f : E → FiberAlt n k` with `ContDiff` regularity and compact support.

## Why this is useful

Stage 1 of the plan aims to define currents as continuous linear functionals on an LF / Fréchet
test-form space, *without* adding ad hoc `bound` fields to the definition of `Current`.

Mathlib provides the LF topology for Euclidean domains; later stages can transport this to
manifolds via charts / partitions of unity.
-/

noncomputable section

open Classical TopologicalSpace

namespace Hodge

open scoped Distributions

/-!
## Euclidean model space

We use `E := EuclideanSpace ℂ (Fin n)` viewed as a real normed space (via restriction of scalars).
-/

abbrev Euclid (n : ℕ) := EuclideanSpace ℂ (Fin n)

/-!
## Euclidean test k-forms (compactly supported)

For an open subset `Ω : Opens (Euclid n)`, a “test k-form” is just a test function
`𝓓(Ω, FiberAlt n k)`.

This is an LF-space (locally convex inductive limit over compact supports), already implemented
in Mathlib.
-/

abbrev EuclidTestForm (n : ℕ) (k : ℕ) (Ω : TopologicalSpace.Opens (Euclid n)) :=
  𝓓(Ω, FiberAlt n k)

/-!
## Euclidean currents (distribution-style)

A “current” on `Ω` acting on test k-forms is modeled as a continuous linear functional:

`EuclidTestForm n k Ω →L[ℝ] ℝ`.

Note: Mathlib's `Distribution Ω F` abbreviations are for ℝ-valued test functions
`𝓓(Ω, ℝ) →L[ℝ] F`. Currents need functionals on **form-valued** test functions, so we define this
directly.
-/

abbrev EuclidCurrent (n : ℕ) (k : ℕ) (Ω : TopologicalSpace.Opens (Euclid n)) :=
  EuclidTestForm n k Ω →L[ℝ] ℝ

end Hodge

end
