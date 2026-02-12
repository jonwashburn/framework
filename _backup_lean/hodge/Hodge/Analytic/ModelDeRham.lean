import Hodge.Analytic.DomCoprod
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Model-space de Rham calculus (Stage 1 of the Mathlib migration).

This file provides **Mathlib-backed** definitions on the model space `ℂⁿ`:

- `ModelForm`: (continuous) differential `k`-forms on `ℂⁿ` as functions
  `E → (E [⋀^Fin k]→L[ℂ] ℂ)`.
- `ModelForm.d`: exterior derivative, defined using Mathlib's `extDeriv`.
- `ModelForm.wedge`: pointwise wedge product, using our `ContinuousAlternatingMap.wedge`.

This is intentionally **model-space only**: upgrading the global `SmoothForm n X k`-based
development to a genuine manifold de Rham complex is Stage 2 (chart glue / invariance).
-/

noncomputable section

open Classical

set_option autoImplicit false

namespace Hodge

/-! ## Forms on the model space `ℂⁿ` -/

abbrev ModelSpace (n : ℕ) := EuclideanSpace ℂ (Fin n)

abbrev ModelForm (n k : ℕ) := ModelSpace n → (ModelSpace n) [⋀^Fin k]→L[ℂ] ℂ

namespace ModelForm

variable {n : ℕ}

/-! ## Exterior derivative -/

noncomputable def d {k : ℕ} (ω : ModelForm n k) : ModelForm n (k + 1) :=
  fun x => extDeriv ω x

@[simp] theorem d_apply {k : ℕ} (ω : ModelForm n k) (x : ModelSpace n) :
    d (n := n) ω x = extDeriv ω x := rfl

theorem d_sq {k : ℕ} {r : WithTop ℕ∞} (ω : ModelForm n k)
    (hω : ContDiff ℂ r ω) (hr : minSmoothness ℂ 2 ≤ r) :
    d (n := n) (d (n := n) ω) = 0 := by
  funext x
  simpa [d] using extDeriv_extDeriv_apply (ω := ω) (x := x) (hω.contDiffAt) hr

/-! ## Wedge product -/

noncomputable def wedge {k l : ℕ} (ω : ModelForm n k) (η : ModelForm n l) :
    ModelForm n (k + l) :=
  fun x => ContinuousAlternatingMap.wedge (ω x) (η x)

@[simp] theorem wedge_apply {k l : ℕ} (ω : ModelForm n k) (η : ModelForm n l) (x : ModelSpace n) :
    wedge (n := n) ω η x = ContinuousAlternatingMap.wedge (ω x) (η x) := rfl

theorem wedge_add_left {k l : ℕ} (ω₁ ω₂ : ModelForm n k) (η : ModelForm n l) :
    wedge (n := n) (ω₁ + ω₂) η = wedge (n := n) ω₁ η + wedge (n := n) ω₂ η := by
  funext x
  ext v
  simp [wedge, ContinuousAlternatingMap.wedge_add_left]

theorem wedge_add_right {k l : ℕ} (ω : ModelForm n k) (η₁ η₂ : ModelForm n l) :
    wedge (n := n) ω (η₁ + η₂) = wedge (n := n) ω η₁ + wedge (n := n) ω η₂ := by
  funext x
  ext v
  simp [wedge, ContinuousAlternatingMap.wedge_add_right]

theorem wedge_smul_left {k l : ℕ} (c : ℂ) (ω : ModelForm n k) (η : ModelForm n l) :
    wedge (n := n) (c • ω) η = c • wedge (n := n) ω η := by
  funext x
  ext v
  simp [wedge, ContinuousAlternatingMap.wedge_smul_left]

theorem wedge_smul_right {k l : ℕ} (c : ℂ) (ω : ModelForm n k) (η : ModelForm n l) :
    wedge (n := n) ω (c • η) = c • wedge (n := n) ω η := by
  funext x
  ext v
  simp [wedge, ContinuousAlternatingMap.wedge_smul_right]

end ModelForm

end Hodge


