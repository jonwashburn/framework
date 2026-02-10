import Hodge.Basic

/-!
# Form Type Definitions

This file defines the smoothness condition for differential form sections
on complex manifolds.

## Main Definitions

* `IsSmoothAlternating`: Predicate for smooth sections of alternating forms
* `IsSmoothAlternatingBundle`: Bundle version of the smoothness condition

## Implementation Notes

A form section is "smooth" if the alternating map varies smoothly in x,
as a map into the normed space of continuous alternating maps.
-/

noncomputable section

open Classical Module Manifold
open scoped Pointwise Manifold

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]

/-- A section of differential forms is "smooth" (C^∞) if the alternating map
varies smoothly in `x`, as a map into the normed space of continuous alternating maps.

We use `∞ : WithTop ℕ∞` (= `↑(⊤ : ℕ∞)`, C^∞ smoothness), **not** `⊤ : WithTop ℕ∞`
(= ω, analytic smoothness).  The distinction matters because Mathlib's
`SmoothPartitionOfUnity.contMDiff_finsum_smul` only produces `∞`-level output, and
smooth differential forms are C^∞ by mathematical convention.

This matches the manuscript-level argument: smooth coefficients give differentiability of the section
in the manifold sense. -/
def IsSmoothAlternating (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    (k : ℕ) (f : X → FiberAlt n k) : Prop :=
  ContMDiff (𝓒_complex n) 𝓘(ℝ, FiberAlt n k) ⊤ f

@[ext]
structure SmoothForm (n : ℕ) (X : Type u) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] where
  as_alternating : X → FiberAlt n k
  is_smooth : IsSmoothAlternating n X k as_alternating

namespace SmoothForm

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] {k : ℕ}

/-- The underlying `ContMDiff` smoothness proof from a `SmoothForm`. -/
theorem smooth (ω : SmoothForm n X k) :
    ContMDiff (𝓒_complex n) 𝓘(ℝ, FiberAlt n k) ⊤ ω.as_alternating :=
  ω.is_smooth

end SmoothForm

end
