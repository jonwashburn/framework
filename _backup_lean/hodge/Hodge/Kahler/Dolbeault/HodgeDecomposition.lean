import Hodge.Cohomology.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Hodge decomposition (skeleton / off proof track)

Sprint 3 (Agent 3) milestone: introduce a compile-stable *interface* for the Hodge decomposition
statement `H^k = ⊕_{p+q=k} H^{p,q}`.

The current proof track for `hodge_conjecture'` does **not** use Dolbeault cohomology, so this
file is intentionally **not imported** by `Hodge.Kahler.Dolbeault` yet.

## Important

This file uses a **placeholder** definition:
- `DolbeaultCohomologyClass n X p q` is currently identified with
  `DeRhamCohomologyClass n X (p+q)`.

With this identification, a “Hodge decomposition” exists for purely formal reasons.
Once genuine `(p,q)`-forms and the `∂̄`-cohomology are implemented, this file should be replaced
by the real statement/proof.
-/

noncomputable section

open Classical
open scoped BigOperators

namespace Hodge

set_option autoImplicit false

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]

/-!
### Placeholder Dolbeault cohomology

To avoid a proliferation of dependent casts in downstream statements, we make the total degree `k`
an *explicit parameter* of the placeholder Dolbeault group.

In the intended development, this should be `H^{p,q}_{∂̄}(X)` with `k = p+q`.
-/

/-- Placeholder for Dolbeault cohomology.

For now this is just the de Rham cohomology group in total degree `k`. -/
abbrev DolbeaultCohomologyClass (n : ℕ) (X : Type u) (k p q : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] : Type u :=
  DeRhamCohomologyClass n X k

namespace DolbeaultCohomologyClass

variable {k p q : ℕ}

/-- The tautological map to de Rham cohomology (placeholder is literally de Rham). -/
def toDeRham :
    DolbeaultCohomologyClass (n := n) (X := X) k p q → DeRhamCohomologyClass n X k :=
  fun c => c

@[simp] lemma toDeRham_apply (c : DolbeaultCohomologyClass (n := n) (X := X) k p q) :
    toDeRham (n := n) (X := X) (k := k) (p := p) (q := q) c = c :=
  rfl

end DolbeaultCohomologyClass

/-- **Hodge decomposition** (placeholder statement).

This is the *shape* of the classical statement, but implemented using the placeholder
`DolbeaultCohomologyClass = DeRhamCohomologyClass`.

In particular, the decomposition we produce is the “stupid” one: everything sits in the
`(0,k)`-slot and the remaining components are `0`. -/
theorem hodge_decomposition_placeholder (k : ℕ) (c : DeRhamCohomologyClass n X k) :
    ∃ decomp :
        (i : Fin (k + 1)) →
          DolbeaultCohomologyClass (n := n) (X := X) k (p := (i : ℕ)) (q := k - (i : ℕ)),
      c = ∑ i : Fin (k + 1),
        DolbeaultCohomologyClass.toDeRham (n := n) (X := X) (k := k) (p := (i : ℕ)) (q := k - (i : ℕ))
          (decomp i) := by
  classical
  let decomp :
      (i : Fin (k + 1)) →
        DolbeaultCohomologyClass (n := n) (X := X) k (p := (i : ℕ)) (q := k - (i : ℕ)) :=
    fun i =>
      dite (i = 0) (fun h => by
          -- For `i = 0`, the type is definitionally `DeRhamCohomologyClass n X k`.
          subst h
          simpa using c)
        (fun _h => 0)
  refine ⟨decomp, ?_⟩
  -- Only the `i = 0` term survives, and the cast is along `0 + (k - 0) = k`.
  -- We use `Finset.sum_eq_single` on `Finset.univ` to kill the `i ≠ 0` summands.
  have hsum :
      (∑ i : Fin (k + 1),
          DolbeaultCohomologyClass.toDeRham (n := n) (X := X) (k := k) (p := (i : ℕ)) (q := k - (i : ℕ))
            (decomp i)) =
        DolbeaultCohomologyClass.toDeRham (n := n) (X := X) (k := k) (p := (0 : ℕ)) (q := k - (0 : ℕ))
          (decomp 0) := by
    simpa using
      (Finset.sum_eq_single (s := (Finset.univ : Finset (Fin (k + 1)))) (a := (0 : Fin (k + 1)))
        (f := fun i =>
          DolbeaultCohomologyClass.toDeRham (n := n) (X := X) (k := k) (p := (i : ℕ)) (q := k - (i : ℕ))
            (decomp i))
        (by
          intro i hi hne
          -- For `i ≠ 0`, `decomp i = 0`, hence the summand is 0.
          simp [decomp, hne])
        (by simp))
  -- Finish by evaluating the surviving `i = 0` term.
  -- The cast is along `0 + (k - 0) = k`, so this is definitionally `c`.
  -- (We keep it short with `simp`.)
  simpa [hsum, decomp, DolbeaultCohomologyClass.toDeRham]

end Hodge
