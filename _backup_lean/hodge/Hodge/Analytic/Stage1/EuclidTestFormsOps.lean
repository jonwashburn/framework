import Hodge.Analytic.DistributionTestForms

import Mathlib.Analysis.Distribution.TestFunction

/-!
# Stage 1 (Euclidean): Basic operations on Euclidean test forms

This is a small, compiling **Stage 1** building block for the plan in
`tex/archive/HodgePlan-mc-28.1.26.rtf`.

We work on Euclidean test `k`-forms as Mathlib test functions
`𝓓(Ω, FiberAlt n k)`, and record a couple of *nontrivial* continuous linear maps
available out of the box:
- inclusion into bounded continuous functions,
- postcomposition by a continuous linear map on the fiber.

These are the first ingredients needed to define currents/distributions as continuous linear
functionals.
-/

noncomputable section

open scoped Distributions BoundedContinuousFunction

namespace Hodge
namespace Analytic
namespace Stage1

open Classical

variable {n : ℕ}
variable {Ω : TopologicalSpace.Opens (Euclid n)}

/-- The canonical inclusion `𝓓(Ω, FiberAlt n k) →L (TangentModel n →ᵇ FiberAlt n k)`. -/
noncomputable def euclidTestForm_toBCF (k : ℕ) :
    EuclidTestForm n k Ω →L[ℝ] (Euclid n →ᵇ FiberAlt n k) :=
  TestFunction.toBoundedContinuousFunctionCLM (n := (⊤ : ℕ∞)) (Ω := Ω) (F := FiberAlt n k) ℝ

/-- Postcomposition on Euclidean test forms by a continuous linear map on the fiber. -/
noncomputable def euclidTestForm_postcompCLM {k k' : ℕ} (T : FiberAlt n k →L[ℝ] FiberAlt n k') :
    EuclidTestForm n k Ω →L[ℝ] EuclidTestForm n k' Ω :=
  TestFunction.postcompCLM (n := (⊤ : ℕ∞)) (Ω := Ω) (𝕜 := ℝ) (F := FiberAlt n k)
    (F' := FiberAlt n k') T

@[simp]
theorem euclidTestForm_postcompCLM_apply {k k' : ℕ} (T : FiberAlt n k →L[ℝ] FiberAlt n k')
    (f : EuclidTestForm n k Ω) :
    euclidTestForm_postcompCLM (n := n) (Ω := Ω) T f = T ∘ f :=
  rfl

end Stage1
end Analytic
end Hodge
