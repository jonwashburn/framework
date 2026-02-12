import Hodge.Analytic.DomCoprod
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Continuous wedge product for ℂ-valued forms over ℝ

Our global de Rham theory is **real-smooth** (base field `ℝ`) but the coefficient field is `ℂ`.
This file defines the wedge product on fibers

`E [⋀^Fin k]→L[ℝ] ℂ`

using Mathlib's algebraic `AlternatingMap.domCoprod` and the multiplication map
`LinearMap.mul' ℝ ℂ : ℂ ⊗[ℝ] ℂ →ₗ[ℝ] ℂ`.

This is the correct wedge for complex-valued differential forms on real manifolds.
-/

noncomputable section

open Classical
open scoped TensorProduct

namespace ContinuousAlternatingMap

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

section

variable [CompleteSpace ℝ]

-- `wedgeℂ_smul_left` / `wedgeℂ_smul_right` are used only to build the curried
-- `wedgeℂCLM_alt`. We postpone their direct proofs to avoid unfolding `domCoprod`
-- down to `domCoprod.summand` (which is brittle and slow here).

/-- The underlying ℝ-linear alternating map used to define `wedgeℂ`. -/
noncomputable def wedgeℂ_linear {k l : ℕ}
    (ω : ContinuousAlternatingMap ℝ E ℂ (Fin k))
    (η : ContinuousAlternatingMap ℝ E ℂ (Fin l)) :
    E [⋀^Fin (k + l)]→ₗ[ℝ] ℂ :=
by
  classical
  -- Use the bilinear `domCoprod'` on tensors of alternating maps, then reindex to `Fin (k+l)`,
  -- and finally multiply in `ℂ` using `LinearMap.mul'`.
  let t :
      TensorProduct ℝ (E [⋀^Fin k]→ₗ[ℝ] ℂ) (E [⋀^Fin l]→ₗ[ℝ] ℂ) :=
    ω.toAlternatingMap ⊗ₜ[ℝ] η.toAlternatingMap
  let domSum : E [⋀^Fin (k + l)]→ₗ[ℝ] (ℂ ⊗[ℝ] ℂ) :=
    (AlternatingMap.domCoprod' (ιa := Fin k) (ιb := Fin l) (R' := ℝ) (Mᵢ := E) (N₁ := ℂ) (N₂ := ℂ) t).domDomCongr
      finSumFinEquiv
  exact (LinearMap.mul' ℝ ℂ).compAlternatingMap domSum

/-- Wedge product of ℂ-valued continuous alternating maps on a real vector space. -/
noncomputable def wedgeℂ {k l : ℕ}
    (ω : ContinuousAlternatingMap ℝ E ℂ (Fin k))
    (η : ContinuousAlternatingMap ℝ E ℂ (Fin l)) :
    ContinuousAlternatingMap ℝ E ℂ (Fin (k + l)) := by
  classical
  let lin : E [⋀^Fin (k + l)]→ₗ[ℝ] ℂ := wedgeℂ_linear ω η
  have h_ex :
      ∃ C : ℝ, ∀ v : Fin (k + l) → E, ‖lin v‖ ≤ C * ∏ i, ‖v i‖ :=
    AlternatingMap.exists_bound_fin_dim (𝕜 := ℝ) (E := E) (F := ℂ) (ι := Fin (k + l)) lin
  refine (lin.mkContinuous (Classical.choose h_ex) (Classical.choose_spec h_ex))

@[simp] theorem wedgeℂ_apply {k l : ℕ}
    (ω : ContinuousAlternatingMap ℝ E ℂ (Fin k))
    (η : ContinuousAlternatingMap ℝ E ℂ (Fin l))
    (v : Fin (k + l) → E) :
    wedgeℂ ω η v = wedgeℂ_linear ω η v := by
  simp [wedgeℂ, wedgeℂ_linear]

@[simp] theorem wedgeℂ_add_left {k l : ℕ}
    (ω₁ ω₂ : ContinuousAlternatingMap ℝ E ℂ (Fin k))
    (η : ContinuousAlternatingMap ℝ E ℂ (Fin l)) :
    wedgeℂ (ω₁ + ω₂) η = wedgeℂ ω₁ η + wedgeℂ ω₂ η := by
  ext v
  -- Reduce to the underlying alternating maps and use bilinearity of tensor products + `domCoprod'`.
  simp [wedgeℂ, wedgeℂ_linear, TensorProduct.add_tmul]

@[simp] theorem wedgeℂ_add_right {k l : ℕ}
    (ω : ContinuousAlternatingMap ℝ E ℂ (Fin k))
    (η₁ η₂ : ContinuousAlternatingMap ℝ E ℂ (Fin l)) :
    wedgeℂ ω (η₁ + η₂) = wedgeℂ ω η₁ + wedgeℂ ω η₂ := by
  ext v
  simp [wedgeℂ, wedgeℂ_linear, TensorProduct.tmul_add]

theorem wedgeℂ_smul_left {k l : ℕ} (c : ℝ)
    (ω : ContinuousAlternatingMap ℝ E ℂ (Fin k))
    (η : ContinuousAlternatingMap ℝ E ℂ (Fin l)) :
    wedgeℂ (c • ω) η = c • wedgeℂ ω η := by
  classical
  -- Work at the level of the underlying alternating maps.
  ext v
  -- Reduce `wedgeℂ` evaluation to `wedgeℂ_linear` evaluation.
  simp [wedgeℂ]
  -- Unfold the definition of `wedgeℂ_linear`; keep it in terms of `domCoprod'`.
  -- The key identity is linearity of `domCoprod'` as a linear map on the tensor input.
  simp [wedgeℂ_linear, AlternatingMap.domDomCongr_smul, LinearMap.compAlternatingMap_smul,
    -AlternatingMap.domCoprod'_apply] at *
  -- Rewrite the tensor in the first argument.
  have ht :
      (c • ω.toAlternatingMap) ⊗ₜ[ℝ] η.toAlternatingMap =
        c • (ω.toAlternatingMap ⊗ₜ[ℝ] η.toAlternatingMap) := by
    simpa using
      (TensorProduct.smul_tmul' (R := ℝ) (r := c) (m := ω.toAlternatingMap) (n := η.toAlternatingMap)).symm
  -- Apply linearity of `domCoprod'` and then of `mul'`.
  -- `domCoprod'` is ℝ-linear: `map_smul` pulls out `c`.
  -- Evaluate at `v ∘ finSumFinEquiv` afterwards.
  simp [ht, map_smul, LinearMap.map_smul]

theorem wedgeℂ_smul_right {k l : ℕ} (c : ℝ)
    (ω : ContinuousAlternatingMap ℝ E ℂ (Fin k))
    (η : ContinuousAlternatingMap ℝ E ℂ (Fin l)) :
    wedgeℂ ω (c • η) = c • wedgeℂ ω η := by
  ext v
  simp [wedgeℂ, wedgeℂ_linear, TensorProduct.tmul_smul]

end

section

variable [CompleteSpace ℝ]

/-- `wedgeℂ` as a bundled bilinear continuous linear map (curried form). -/
noncomputable def wedgeℂCLM_alt (k l : ℕ) :
    (ContinuousAlternatingMap ℝ E ℂ (Fin k)) →L[ℝ]
      (ContinuousAlternatingMap ℝ E ℂ (Fin l) →L[ℝ]
        ContinuousAlternatingMap ℝ E ℂ (Fin (k + l))) :=
by
  classical
  -- We just curry the bilinear operation `wedgeℂ`.
  refine
    LinearMap.toContinuousLinearMap (𝕜 := ℝ)
        (E := ContinuousAlternatingMap ℝ E ℂ (Fin k))
        (F' := (ContinuousAlternatingMap ℝ E ℂ (Fin l) →L[ℝ]
          ContinuousAlternatingMap ℝ E ℂ (Fin (k + l)))) ?_
  refine
    { toFun := fun ω =>
        LinearMap.toContinuousLinearMap (𝕜 := ℝ)
            (E := ContinuousAlternatingMap ℝ E ℂ (Fin l))
            (F' := ContinuousAlternatingMap ℝ E ℂ (Fin (k + l))) ?_
      map_add' := ?_
      map_smul' := ?_ }
  · refine
      { toFun := fun η => wedgeℂ (ω := ω) (η := η)
        map_add' := fun a b => wedgeℂ_add_right (ω := ω) (η₁ := a) (η₂ := b)
        map_smul' := fun c a => wedgeℂ_smul_right (c := c) (ω := ω) (η := a) }
  · intro a b
    ext η v
    simp [wedgeℂ_add_left]
  · intro c a
    ext η v
    simp [wedgeℂ_smul_left]

end

end ContinuousAlternatingMap
