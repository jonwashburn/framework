import Hodge.Cohomology.Basic

/-!
# sl(2) representation theory (skeleton / off proof track)

Sprint 4 (Agent 3) milestone: state the representation-theoretic bijectivity behind Hard Lefschetz.

## Mathematical statement (informal)

On a compact Kähler manifold of complex dimension `n`, the Lefschetz operator
\(L(\alpha) = [\omega] \smile \alpha\) satisfies that for `k ≤ n`,
\(L^{n-k} : H^k(X) \to H^{2n-k}(X)\) is an isomorphism.

## Implementation status

This file provides a **compile-stable interface** for the bijectivity statement used in
Hard Lefschetz proofs.  The real proof (via Kähler identities + primitive decomposition +
finite-dimensional sl(2) representation theory) is substantial.

To avoid admitted proofs while keeping the statement usable, we package the bijectivity as an
explicit **assumption** `HardLefschetzData` (a Classical Pillar *off* the main proof track).

This module is **off proof track** unless explicitly imported.
-/

noncomputable section

open Classical

namespace Hodge

set_option autoImplicit false

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X]
  [K : KahlerManifold n X]

/-! ## Lefschetz power map induced by the Kähler class -/

/-- The Kähler class `[ω] ∈ H²(X)` (as a de Rham cohomology class). -/
noncomputable def kahlerClass : DeRhamCohomologyClass n X 2 :=
  ⟦K.omega_form, K.omega_closed⟧

/-- Iterated Lefschetz operator `L^r` on de Rham cohomology, induced by the Kähler class.

This is just `lefschetz_power_of_class` specialized to `[ω]`. -/
noncomputable def lefschetzPower (p r : ℕ) :
    DeRhamCohomologyClass n X p →ₗ[ℂ] DeRhamCohomologyClass n X (p + 2 * r) :=
  lefschetz_power_of_class (n := n) (X := X) (ω := kahlerClass (n := n) (X := X)) p r

/-! ## Bijectivity statement (Hard Lefschetz via sl(2)) -/

/-- **Hard Lefschetz data** (Classical Pillar, off proof track).

This packages the bijectivity of the Lefschetz power map induced by the Kähler class:
for `k ≤ n`, the map `L^(n-k) : H^k → H^(k + 2*(n-k))` is bijective. -/
class HardLefschetzData (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] : Prop where
  bijective : ∀ k : ℕ, k ≤ n →
    Function.Bijective (lefschetzPower (n := n) (X := X) (p := k) (r := n - k))

/-- **sl(2) bijectivity (Hard Lefschetz form)**.

For `k ≤ n`, the iterated Lefschetz operator

`L^(n-k) : H^k → H^(k + 2*(n-k))`

is bijective (and `k + 2*(n-k) = 2*n - k` when `k ≤ n`).

This theorem is currently provided by the `HardLefschetzData` assumption. -/
theorem sl2_representation_bijectivity (k : ℕ) (hk : k ≤ n)
    [HardLefschetzData (n := n) (X := X)] :
    Function.Bijective (lefschetzPower (n := n) (X := X) (p := k) (r := n - k)) :=
  HardLefschetzData.bijective (n := n) (X := X) k hk

end Hodge
