import Hodge.Analytic.Laplacian.HodgeLaplacian

/-!
# Harmonic Forms

A `k`-form is **harmonic** if its Laplacian vanishes.
This file provides the basic definition and the associated kernel submodule.
-/

noncomputable section

open Classical

set_option autoImplicit false

universe u

variable {n : ℕ} {X : Type u}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]

/-- A form is harmonic if its Laplacian vanishes. -/
def IsHarmonic {k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ 2 * n) (ω : SmoothForm n X k) : Prop :=
  laplacian_construct (n := n) (X := X) (k := k) hk hk' ω = 0

/-- The space of harmonic `k`-forms as the kernel of the Laplacian linear map. -/
noncomputable def HarmonicSubmodule (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 2 * n) :
    Submodule ℂ (SmoothForm n X k) :=
  (laplacianLinearMap (n := n) (X := X) k hk hk').ker

/-- `IsHarmonic` is membership in `ker(Δ)`. -/
theorem isHarmonic_iff_mem_harmonicSubmodule {k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ 2 * n)
    (ω : SmoothForm n X k) :
    IsHarmonic (n := n) (X := X) hk hk' ω ↔
      ω ∈ HarmonicSubmodule (n := n) (X := X) k hk hk' := by
  simp [IsHarmonic, HarmonicSubmodule, laplacianLinearMap]

@[simp] theorem isHarmonic_zero {k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ 2 * n) :
    IsHarmonic (n := n) (X := X) hk hk' (0 : SmoothForm n X k) := by
  simp [IsHarmonic, laplacian_construct_zero, hk, hk']

theorem isHarmonic_add {k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ 2 * n)
    {α β : SmoothForm n X k} :
    IsHarmonic (n := n) (X := X) hk hk' α →
      IsHarmonic (n := n) (X := X) hk hk' β →
        IsHarmonic (n := n) (X := X) hk hk' (α + β) := by
  intro hα hβ
  simp [IsHarmonic, laplacian_construct_add, hα, hβ]

theorem isHarmonic_smul {k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ 2 * n)
    (c : ℂ) {α : SmoothForm n X k} :
    IsHarmonic (n := n) (X := X) hk hk' α →
      IsHarmonic (n := n) (X := X) hk hk' (c • α) := by
  intro hα
  simp [IsHarmonic, laplacian_construct_smul, hα]

theorem isHarmonic_neg {k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ 2 * n)
    {α : SmoothForm n X k} :
    IsHarmonic (n := n) (X := X) hk hk' α →
      IsHarmonic (n := n) (X := X) hk hk' (-α) := by
  intro hα
  simpa using (isHarmonic_smul (n := n) (X := X) hk hk' (-1 : ℂ) hα)

theorem isHarmonic_sub {k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ 2 * n)
    {α β : SmoothForm n X k} :
    IsHarmonic (n := n) (X := X) hk hk' α →
      IsHarmonic (n := n) (X := X) hk hk' β →
        IsHarmonic (n := n) (X := X) hk hk' (α - β) := by
  intro hα hβ
  have hneg : IsHarmonic (n := n) (X := X) hk hk' (-β) :=
    isHarmonic_neg (n := n) (X := X) hk hk' (α := β) hβ
  simpa [sub_eq_add_neg] using
    (isHarmonic_add (n := n) (X := X) hk hk' (α := α) (β := -β) hα hneg)
