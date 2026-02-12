import Hodge.Analytic.Laplacian.HodgeLaplacian

/-!
# Harmonic forms (skeleton / off proof track)

This file introduces a lightweight interface for *harmonic forms*:

- A `k`-form `ω` is harmonic if `Δω = 0`.

This file provides a small interface (definition only). The deeper theorems
relating harmonicity to closed/coclosed forms and to Hodge decomposition are not developed here.

This module is **off proof track** unless explicitly imported.
-/

noncomputable section

open Classical

namespace Hodge
namespace HarmonicForms

set_option autoImplicit false

universe u

variable {n : ℕ} {X : Type u}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]

/-- A form is harmonic if its Laplacian vanishes. -/
def IsHarmonic {k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ n) (ω : SmoothForm n X k) : Prop :=
  HodgeLaplacian.laplacian_construct (n := n) (X := X) (k := k) hk hk' ω = 0

/-- The space of harmonic `k`-forms as the kernel of the Laplacian linear map. -/
noncomputable def HarmonicSubmodule (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ n) :
    Submodule ℂ (SmoothForm n X k) :=
  (HodgeLaplacian.laplacianLinearMap (n := n) (X := X) k hk hk').ker

/-- `IsHarmonic` is literally membership in `ker(Δ)` (the kernel submodule). -/
theorem isHarmonic_iff_mem_harmonicSubmodule {k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ n)
    (ω : SmoothForm n X k) :
    IsHarmonic (n := n) (X := X) hk hk' ω ↔
      ω ∈ HarmonicSubmodule (n := n) (X := X) k hk hk' := by
  -- `x ∈ ker(f)` is definitionally `f x = 0`.
  simp [IsHarmonic, HarmonicSubmodule, HodgeLaplacian.laplacianLinearMap]

/-!
## Not (yet) in this repo

The classical characterization

`Δω = 0 ↔ (dω = 0 ∧ δω = 0)`

uses the L² inner product and Stokes' theorem; it is not developed here.
-/

end HarmonicForms
end Hodge
