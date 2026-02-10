import Hodge.Kahler.Identities.Sl2
import Hodge.Kahler.Lefschetz.PrimitiveDecomp
import Hodge.Kahler.Lefschetz.Sl2Representation
import Hodge.Classical.Lefschetz

/-!
# Lefschetz / sl(2) Connection Tests (Round 3, Agent 4)

This file is a lightweight compilation test-suite for the Lefschetz/sl(2) layer.

It intentionally contains **no admitted proofs** and is **off the main proof track**.
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

/-! ## sl(2) relations (form-level placeholders) -/

example (k : ℕ) (ω : SmoothForm n X k) :
    Sl2.weightOperator (n := n) (X := X) k ω = (k - n : ℂ) • ω := by
  simpa using (Sl2.weightOperator_apply (n := n) (X := X) (k := k) ω)

/-! ## Primitive decomposition API compiles -/

example {k : ℕ} (hk : k ≥ 2) :
    Submodule ℂ (DeRhamCohomologyClass n X k) :=
  PrimitiveCohomology (n := n) (X := X) k hk

example {k : ℕ} (hk : k ≥ 2) (c : DeRhamCohomologyClass n X k) :
    IsPrimitive (n := n) (X := X) hk c ↔ c ∈ PrimitiveCohomology (n := n) (X := X) k hk :=
  isPrimitive_iff_mem (n := n) (X := X) hk c

/-! ## Hard Lefschetz interface compiles (cohomology-level) -/

variable [HardLefschetzData (n := n) (X := X)]

example (k : ℕ) (hk : k ≤ n) :
    Function.Bijective (lefschetzPower (n := n) (X := X) (p := k) (r := n - k)) :=
  sl2_representation_bijectivity (n := n) (X := X) (k := k) hk

example (k : ℕ) (hk : k ≤ n) :
    DeRhamCohomologyClass n X k ≃ₗ[ℂ] DeRhamCohomologyClass n X (k + 2 * (n - k)) :=
  hardLefschetzEquiv (n := n) (X := X) k hk

example (k : ℕ) (hk : k ≤ n) :
    DeRhamCohomologyClass n X (k + 2 * (n - k)) →ₗ[ℂ] DeRhamCohomologyClass n X k :=
  lefschetz_inverse_cohomology (n := n) (X := X) k hk

example (k : ℕ) (hk : k ≤ n) (c : DeRhamCohomologyClass n X k) :
    lefschetz_inverse_cohomology (n := n) (X := X) k hk
        ((lefschetzPower (n := n) (X := X) (p := k) (r := n - k)) c) = c :=
  lefschetz_inverse_left_inv (n := n) (X := X) k hk c

end Hodge
