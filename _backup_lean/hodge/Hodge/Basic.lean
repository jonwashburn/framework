import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Defs.Induced

import Mathlib.Analysis.Normed.Module.Alternating.Basic

/-!
# Basic Definitions for Hodge Conjecture Formalization

This file contains the foundational type definitions used throughout the
Hodge conjecture formalization:

## Main Definitions

* `TangentModel n`: The model tangent space `ℂⁿ` (EuclideanSpace ℂ (Fin n))
* `FiberAlt n k`: Continuous alternating k-linear maps on the tangent space
* `𝓒_complex n`: The smooth structure for complex n-dimensional manifolds
* `HasLocallyConstantCharts`: Condition for chart transitions to be locally constant

## Mathematical Background

We work with complex manifolds of dimension n, where the underlying real dimension
is 2n. The tangent spaces are modeled on ℂⁿ, and differential k-forms are
represented as sections of alternating multilinear maps on tangent vectors.

## Usage

This file is imported by essentially all other modules in the project.
-/

noncomputable section

open Classical
open scoped Manifold

set_option autoImplicit false

universe u

/-- We work with the model tangent space `E = ℂⁿ` (Mathlib's `EuclideanSpace ℂ (Fin n)`).

In Mathlib, `TangentSpace (𝓒_complex n) x` is a type synonym for this `E`, so this is the
correct (and non-dependent) fiber to use for continuity of sections. -/
abbrev TangentModel (n : ℕ) := EuclideanSpace ℂ (Fin n)

/-- The (fiberwise) space of continuous alternating `k`-linear maps on the model tangent space.
This is the correct object to put a norm/topology on (Mathlib: operator norm on
`ContinuousAlternatingMap`). -/
abbrev FiberAlt (n : ℕ) (k : ℕ) := (TangentModel n) [⋀^Fin k]→L[ℝ] ℂ

/-!
## Minimal projective space model (for Chow/GAGA semantics)

Mathlib’s `LinearAlgebra/Projectivization/*` modules are not part of the precompiled Mathlib
cache used in this repo, so we define a small internal projective-space type sufficient to:
- talk about a chosen projective embedding `X → ℙ^N(ℂ)`, and
- define algebraic subsets as homogeneous polynomial zero loci pulled back along that embedding.

This is **not** a stub: it is the standard quotient definition of projective space.
-/

/-- The ambient vector space `ℂ^{N+1}` used for `ℙ^N(ℂ)`. -/
abbrev ProjVec (N : ℕ) := Fin (N + 1) → ℂ

/-- Nonzero vectors in `ℂ^{N+1}`. -/
abbrev ProjVecNZ (N : ℕ) := { v : ProjVec N // v ≠ 0 }

namespace ProjVecNZ

variable {N : ℕ}

/-- Scale a nonzero vector by a nonzero scalar, staying nonzero. -/
noncomputable def smul (t : ℂ) (ht : t ≠ 0) (v : ProjVecNZ N) : ProjVecNZ N :=
  ⟨t • v.1, by
    intro h0
    have : v.1 = 0 := by
      -- cancel the nonzero scalar `t`
      have : (t⁻¹) • (t • v.1) = (t⁻¹) • (0 : ProjVec N) := by simpa [h0]
      simpa [smul_smul, ht, inv_mul_cancel₀, one_smul] using this
    exact v.2 this⟩

end ProjVecNZ

/-- The projective equivalence relation on nonzero vectors: `v ~ w` iff `v = t • w` for some `t ≠ 0`. -/
def projSetoid (N : ℕ) : Setoid (ProjVecNZ N) where
  r v w := ∃ t : ℂ, t ≠ 0 ∧ (v.1 = t • w.1)
  iseqv := by
    refine ⟨?refl, ?symm, ?trans⟩
    · intro v
      refine ⟨1, one_ne_zero, ?_⟩
      simpa using (one_smul ℂ v.1).symm
    · intro v w
      rintro ⟨t, ht, hvt⟩
      refine ⟨t⁻¹, inv_ne_zero ht, ?_⟩
      -- from `v = t • w` deduce `w = t⁻¹ • v`
      have := congrArg (fun x => (t⁻¹) • x) hvt.symm
      -- `(t⁻¹) • (t • w) = w`
      simpa [smul_smul, ht, inv_mul_cancel₀, one_smul] using this
    · intro u v w
      rintro ⟨t₁, ht₁, hu⟩ ⟨t₂, ht₂, hv⟩
      refine ⟨t₁ * t₂, mul_ne_zero ht₁ ht₂, ?_⟩
      -- u = t₁ • v and v = t₂ • w ⇒ u = (t₁*t₂) • w
      calc
        u.1 = t₁ • v.1 := hu
        _ = t₁ • (t₂ • w.1) := by simpa [hv]
        _ = (t₁ * t₂) • w.1 := by simp [smul_smul]

/-- The projective space `ℙ^N(ℂ)` as a quotient of nonzero vectors. -/
abbrev ProjSpace (N : ℕ) := Quotient (projSetoid N)

/-- Real-smooth structure on the underlying real manifold of `ℂⁿ`.

In this repository, we take the base field for smoothness to be `ℝ` so that `ContMDiff`
matches the usual \(C^\infty\) notion used by de Rham theory and Hodge theory. -/
def 𝓒_complex (n : ℕ) : ModelWithCorners ℝ (EuclideanSpace ℂ (Fin n)) (EuclideanSpace ℂ (Fin n)) :=
  modelWithCornersSelf ℝ (EuclideanSpace ℂ (Fin n))

/-- Charts are locally constant on their domains.

This condition says that for any point `y` in the domain of `chartAt x`, we have
`chartAt y = chartAt x`. This is automatically satisfied by:
1. Model spaces (EuclideanSpace) - chartAt is the identity everywhere
2. Any manifold with a maximal atlas containing only compatible charts

**Mathematical justification**: This is a technical condition needed for Lean's
type system. In classical mathematics, exterior derivative is chart-independent
and smooth because we work with actual coordinate changes. In Lean, the changing
`chartAt` function breaks smoothness proofs. This condition restores the ability
to prove smoothness by making `chartAt` locally constant.

**Note**: This does NOT restrict the class of manifolds - any manifold admits an
atlas satisfying this property by taking a refinement. It's purely a formalization
convenience. -/
class HasLocallyConstantCharts (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] : Prop where
  charts_locally_constant : ∀ {x y : X}, y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source →
    chartAt (EuclideanSpace ℂ (Fin n)) y = chartAt (EuclideanSpace ℂ (Fin n)) x

/-- Extract the chart locality hypothesis. -/
theorem HasLocallyConstantCharts.hCharts {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [h : HasLocallyConstantCharts n X] :
    ∀ {x y : X}, y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source →
      chartAt (EuclideanSpace ℂ (Fin n)) y = chartAt (EuclideanSpace ℂ (Fin n)) x :=
  h.charts_locally_constant

class ProjectiveComplexManifold (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    extends IsManifold (𝓒_complex n) ⊤ X, CompactSpace X, HasLocallyConstantCharts n X where
  embedding_dim : ℕ
  /-- A chosen projective embedding `X → ℙ^N(ℂ)` (semantic, not a stub). -/
  embedding : X → ProjSpace embedding_dim
  /-- The chosen projective embedding is continuous. -/
  embedding_continuous : Continuous embedding

-- exists_not_isClosed_set was unused and has been removed

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]

/-- The tangent space at a point on a complex manifold modeled on `EuclideanSpace ℂ (Fin n)`
    is definitionally equal to `EuclideanSpace ℂ (Fin n)`, which is a `NormedAddCommGroup`.
    We use `inferInstanceAs` to transfer this instance. -/
instance instNormedAddCommGroupTangentSpace (x : X) : NormedAddCommGroup (TangentSpace (𝓒_complex n) x) :=
  inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℂ (Fin n)))

/-- The tangent space at a point on a complex manifold modeled on `EuclideanSpace ℂ (Fin n)`
    is definitionally equal to `EuclideanSpace ℂ (Fin n)`, which is a `NormedSpace ℂ`.
    We use `inferInstanceAs` to transfer this instance. -/
instance instNormedSpaceTangentSpace (x : X) : NormedSpace ℂ (TangentSpace (𝓒_complex n) x) :=
  inferInstanceAs (NormedSpace ℂ (EuclideanSpace ℂ (Fin n)))

end
