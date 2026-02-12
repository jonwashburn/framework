import Hodge.Kahler.TypeDecomposition

/-!
# Dolbeault: (p,q)-Type Decomposition (Lightweight Interface)

This module provides a minimal interface for talking about (p,q)-type and
“projection onto type” operators, sufficient for downstream Dolbeault operators.

**Note**: The full analytic `(p,q)`-splitting is not currently on the proof track
for `hodge_conjecture'`.  We therefore implement a conservative, compile-friendly
API that can be strengthened later.
-/

noncomputable section

open Classical Hodge

set_option autoImplicit false

universe u

variable {n : ℕ} {X : Type u}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]

/-- A smooth form `ω` has pure `(p,q)`-type.

Currently this is a wrapper around the existing inductive predicate `isPQForm`
from `Hodge.Kahler.TypeDecomposition`. -/
def isPureType (p q : ℕ) (ω : SmoothForm n X (p + q)) : Prop :=
  isPQForm n X p q (by rfl) ω

/-- Projection onto the `(p,q)`-component (placeholder).

At the moment we use the identity projection; the real `(p,q)`-splitting can
replace this definition later without changing downstream interfaces. -/
noncomputable def typeProjection (p q : ℕ) {k : ℕ} (_hpq : p + q = k) :
    SmoothForm n X k →ₗ[ℂ] SmoothForm n X k :=
  LinearMap.id

@[simp] theorem typeProjection_apply (p q : ℕ) {k : ℕ} (hpq : p + q = k) (ω : SmoothForm n X k) :
    typeProjection (n := n) (X := X) p q hpq ω = ω :=
  rfl

end
