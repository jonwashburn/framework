import Hodge.Kahler.Lefschetz.Sl2Representation

/-!
# Classical: Hard Lefschetz (via sl(2)) — Interface

This module provides a **usable interface** for Hard Lefschetz isomorphisms in terms of the
`sl(2)`-style bijectivity statement.

## Proof status

In this repository’s current architecture, Hard Lefschetz is **off the main proof track** for
`hodge_conjecture'`.  We therefore avoid admitted proofs by packaging the bijectivity assumption as the
typeclass `Hodge.HardLefschetzData` (see `Hodge/Kahler/Lefschetz/Sl2Representation.lean`).

Once a genuine sl(2) representation-theoretic proof is formalized, this file can be upgraded
by providing an instance of `HardLefschetzData` from those proofs.
-/

noncomputable section

open Classical

namespace Hodge

set_option autoImplicit false

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]

/-- The Hard Lefschetz linear equivalence `L^(n-k) : H^k → H^(k+2*(n-k))`,
constructed from the bijectivity data. -/
noncomputable def hardLefschetzEquiv (k : ℕ) (hk : k ≤ n)
    [HardLefschetzData (n := n) (X := X)] :
    DeRhamCohomologyClass n X k ≃ₗ[ℂ] DeRhamCohomologyClass n X (k + 2 * (n - k)) :=
  LinearEquiv.ofBijective
    (lefschetzPower (n := n) (X := X) (p := k) (r := n - k))
    (sl2_representation_bijectivity (n := n) (X := X) (k := k) hk)

/-- The inverse Lefschetz map `L^(n-k)^{-1}` as a linear map. -/
noncomputable def lefschetz_inverse_cohomology (k : ℕ) (hk : k ≤ n)
    [HardLefschetzData (n := n) (X := X)] :
    DeRhamCohomologyClass n X (k + 2 * (n - k)) →ₗ[ℂ] DeRhamCohomologyClass n X k :=
  (hardLefschetzEquiv (n := n) (X := X) k hk).symm.toLinearMap

/-- Left inverse property: `L^(n-k)^{-1} (L^(n-k) c) = c`. -/
theorem lefschetz_inverse_left_inv (k : ℕ) (hk : k ≤ n)
    [HardLefschetzData (n := n) (X := X)]
    (c : DeRhamCohomologyClass n X k) :
    lefschetz_inverse_cohomology (n := n) (X := X) k hk
        ((lefschetzPower (n := n) (X := X) (p := k) (r := n - k)) c) = c := by
  -- Convert to the `LinearEquiv` statement.
  change (hardLefschetzEquiv (n := n) (X := X) k hk).symm
        ((hardLefschetzEquiv (n := n) (X := X) k hk) c) = c
  exact (hardLefschetzEquiv (n := n) (X := X) k hk).symm_apply_apply c

/-- Right inverse property: `L^(n-k) (L^(n-k)^{-1} c) = c`. -/
theorem lefschetz_inverse_right_inv (k : ℕ) (hk : k ≤ n)
    [HardLefschetzData (n := n) (X := X)]
    (c : DeRhamCohomologyClass n X (k + 2 * (n - k))) :
    (lefschetzPower (n := n) (X := X) (p := k) (r := n - k))
        (lefschetz_inverse_cohomology (n := n) (X := X) k hk c) = c := by
  -- Convert to the `LinearEquiv` statement.
  change (hardLefschetzEquiv (n := n) (X := X) k hk)
        ((hardLefschetzEquiv (n := n) (X := X) k hk).symm c) = c
  exact (hardLefschetzEquiv (n := n) (X := X) k hk).apply_symm_apply c

end Hodge
