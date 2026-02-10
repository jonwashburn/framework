import Hodge.Analytic.Forms
import Mathlib.Tactic.Ring
import Hodge.Kahler.Dolbeault.TypeDecomposition

/-!
# Dolbeault Operators (∂ and ∂̄)

This module defines the Dolbeault operators as ℂ-linear maps on smooth forms.

In a full development these are obtained by projecting the exterior derivative `d`
to its holomorphic/antiholomorphic components using the complex structure.

For now (and off the main proof track), we provide a compile-stable interface:
- `dolbeault` and `dolbeaultBar` are *both* defined as \(\tfrac12 d\).

This choice makes the basic identities provable without introducing new axioms,
and can be refined later without changing downstream statements.
-/

noncomputable section

open Classical Hodge

set_option autoImplicit false

universe u

variable {n : ℕ} {X : Type u}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]

/-- The Dolbeault operator `∂` (placeholder): currently `∂ := (1/2)·d`. -/
noncomputable def dolbeault (k : ℕ) :
    SmoothForm n X k →ₗ[ℂ] SmoothForm n X (k + 1) :=
  (2⁻¹ : ℂ) • extDerivLinearMap n X k

/-- The Dolbeault operator `∂̄` (placeholder): currently `∂̄ := (1/2)·d`. -/
noncomputable def dolbeaultBar (k : ℕ) :
    SmoothForm n X k →ₗ[ℂ] SmoothForm n X (k + 1) :=
  (2⁻¹ : ℂ) • extDerivLinearMap n X k

@[simp] theorem dolbeault_apply {k : ℕ} (ω : SmoothForm n X k) :
    dolbeault (n := n) (X := X) k ω =
      (2⁻¹ : ℂ) • smoothExtDeriv (n := n) (X := X) (k := k) ω :=
  rfl

@[simp] theorem dolbeaultBar_apply {k : ℕ} (ω : SmoothForm n X k) :
    dolbeaultBar (n := n) (X := X) k ω =
      (2⁻¹ : ℂ) • smoothExtDeriv (n := n) (X := X) (k := k) ω :=
  rfl

/-- `d = ∂ + ∂̄` (by our placeholder definitions). -/
theorem d_eq_dolbeault_sum {k : ℕ} (ω : SmoothForm n X k) :
    smoothExtDeriv (n := n) (X := X) (k := k) ω =
      dolbeault (n := n) (X := X) k ω + dolbeaultBar (n := n) (X := X) k ω := by
  -- Both `∂` and `∂̄` are `(1/2)·d`, so their sum is `d`.
  -- Reduce to an equality in the ℂ-module `SmoothForm`.
  simp [dolbeault, dolbeaultBar, smoothExtDeriv]
  -- Scalar arithmetic in ℂ.
  have h : (2⁻¹ : ℂ) + (2⁻¹ : ℂ) = (1 : ℂ) := by
    -- Use `1/2 + 1/2 = 1` and simplify `1/2` to `2⁻¹`.
    have h' : (1 / 2 : ℂ) + (1 / 2 : ℂ) = (1 : ℂ) := by ring
    simpa [one_div] using h'
  -- Combine the two identical terms.
  calc
    (extDerivLinearMap n X k) ω = (1 : ℂ) • (extDerivLinearMap n X k) ω := by simp
    _ = ((2⁻¹ : ℂ) + (2⁻¹ : ℂ)) • (extDerivLinearMap n X k) ω := by simpa [h]
    _ = (2⁻¹ : ℂ) • (extDerivLinearMap n X k) ω + (2⁻¹ : ℂ) • (extDerivLinearMap n X k) ω := by
          simp [add_smul]

/-- `∂̄ ∘ ∂̄ = 0` (follows from `d² = 0`). -/
theorem dolbeaultBar_squared (k : ℕ) :
    (dolbeaultBar (n := n) (X := X) (k := k + 1)).comp (dolbeaultBar (n := n) (X := X) (k := k)) = 0 := by
  ext ω
  -- `∂̄ = (1/2)·d`, so `∂̄² = (1/4)·d² = 0`.
  simp [dolbeaultBar, LinearMap.comp_apply]
  -- Push the scalar through `d` using linearity.
  have hsmul :
      (extDerivLinearMap n X (k + 1)) ((2⁻¹ : ℂ) • (extDerivLinearMap n X k) ω) =
        (2⁻¹ : ℂ) • (extDerivLinearMap n X (k + 1)) ((extDerivLinearMap n X k) ω) := by
    simpa using (extDerivLinearMap n X (k + 1)).map_smul (2⁻¹ : ℂ) ((extDerivLinearMap n X k) ω)
  -- Use `d² = 0`.
  have hdd : (extDerivLinearMap n X (k + 1)) ((extDerivLinearMap n X k) ω) = 0 := by
    simpa [smoothExtDeriv] using (smoothExtDeriv_extDeriv (n := n) (X := X) (k := k) ω)
  -- Finish.
  simp [hsmul, hdd, smul_smul, mul_assoc]

end
