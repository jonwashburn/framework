import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Continuous Wedge Product (domCoprod)

This file is a **local overlay** used by the Hodge project.

Mathlib currently provides `AlternatingMap.domCoprod` (algebraic wedge product), but does not yet
package a corresponding `ContinuousAlternatingMap` construction in the version pinned by this repo.

This module provides the continuous version of the wedge product and its basic algebraic properties.
-/

open TensorProduct

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

section FiniteDimensionalInstances

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {ι : Type*} [Fintype ι]

instance instFiniteDimensional_alternatingMap
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] :
    FiniteDimensional 𝕜 (E [⋀^ι]→ₗ[𝕜] F) := by
  classical
  let f : (E [⋀^ι]→ₗ[𝕜] F) →ₗ[𝕜] MultilinearMap 𝕜 (fun _ : ι => E) F :=
    AlternatingMap.toMultilinearMapLM (R := 𝕜) (S := 𝕜) (M := E) (N := F) (ι := ι)
  have hf_inj : Function.Injective f := by
    intro a b hab
    ext v
    have : (f a : (ι → E) → F) = (f b : (ι → E) → F) := by
      simpa using
        congrArg
          (fun (g : MultilinearMap 𝕜 (fun _ : ι => E) F) => (g : (ι → E) → F))
          hab
    exact congrArg (fun g => g v) this
  exact FiniteDimensional.of_injective f hf_inj

instance instFiniteDimensional_continuousAlternatingMap
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] :
    FiniteDimensional 𝕜 (E [⋀^ι]→L[𝕜] F) := by
  classical
  let f : (E [⋀^ι]→L[𝕜] F) →ₗ[𝕜] (E [⋀^ι]→ₗ[𝕜] F) :=
    ContinuousAlternatingMap.toAlternatingMapLinear (R := 𝕜) (A := 𝕜) (M := E) (N := F) (ι := ι)
  have hf_inj : Function.Injective f := by
    intro a b hab
    apply ContinuousAlternatingMap.ext
    intro v
    have : (f a : (ι → E) → F) = (f b : (ι → E) → F) := by
      simpa using congrArg (fun (g : E [⋀^ι]→ₗ[𝕜] F) => (g : (ι → E) → F)) hab
    exact congrArg (fun g => g v) this
  exact FiniteDimensional.of_injective f hf_inj

end FiniteDimensionalInstances

theorem MultilinearMap.continuous_of_finiteDimensional {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : MultilinearMap 𝕜 (fun _ : ι => E) F) :
    Continuous f := by
  cases isEmpty_or_nonempty ι with
  | inl hι =>
    have : f = (MultilinearMap.constOfIsEmpty 𝕜 _ (f default)) := by
      ext v; simp [Subsingleton.elim v default]
    rw [this]
    exact continuous_const
  | inr hι =>
    let n := Module.finrank 𝕜 E
    let b := Module.finBasis 𝕜 E
    have key : ∀ v, f v = ∑ r : ι → Fin n, (∏ i, b.repr (v i) (r i)) • f (fun i => b (r i)) := by
      intro v
      conv_lhs => rw [show v = (fun i => ∑ j, (b.repr (v i) j) • b j) from
        funext (fun i => (b.sum_repr (v i)).symm)]
      rw [f.map_sum]
      congr 1
      ext r
      rw [f.map_smul_univ]
    let g : (ι → E) → F := fun v =>
      ∑ r : ι → Fin n, (∏ i, b.repr (v i) (r i)) • f (fun i => b (r i))
    have hg_eq : (f : (ι → E) → F) = g := funext key
    rw [hg_eq]
    apply continuous_finset_sum
    intro r _
    apply Continuous.smul
    · apply continuous_finset_prod
      intro i _
      have : (fun v : ι → E => b.repr (v i) (r i)) =
             (fun e : E => b.repr e (r i)) ∘ (fun v : ι → E => v i) := rfl
      rw [this]
      apply Continuous.comp
      · let coordj : E →ₗ[𝕜] 𝕜 := (Finsupp.lapply (r i)).comp b.repr.toLinearMap
        exact LinearMap.continuous_of_finiteDimensional coordj
      · exact continuous_apply i
    · exact continuous_const

theorem AlternatingMap.exists_bound_fin_dim {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : E [⋀^ι]→ₗ[𝕜] F) :
    ∃ C : ℝ, ∀ v : ι → E, ‖f v‖ ≤ C * ∏ i, ‖v i‖ := by
  let f_multi := f.toMultilinearMap
  have hcont : Continuous f_multi := MultilinearMap.continuous_of_finiteDimensional f_multi
  obtain ⟨C, _, hC⟩ := f_multi.exists_bound_of_continuous hcont
  exact ⟨C, hC⟩

noncomputable section

namespace ContinuousAlternatingMap

variable [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜]

def domDomCongr {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ι' : Type*} [Fintype ι'] [DecidableEq ι']
    (f : ContinuousAlternatingMap 𝕜 E F ι) (e : ι ≃ ι') :
    ContinuousAlternatingMap 𝕜 E F ι' where
  toAlternatingMap := f.toAlternatingMap.domDomCongr e
  cont := f.cont.comp (continuous_pi fun i => continuous_apply (e i))

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
@[simp]
theorem domDomCongr_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ι' : Type*} [Fintype ι'] [DecidableEq ι']
    (f : ContinuousAlternatingMap 𝕜 E F ι) (e : ι ≃ ι') (v : ι' → E) :
    f.domDomCongr e v = f (v ∘ e) := rfl

noncomputable def wedgeAlternatingTensor {k l : ℕ}
    (t :
      TensorProduct 𝕜 (E [⋀^Fin k]→ₗ[𝕜] 𝕜) (E [⋀^Fin l]→ₗ[𝕜] 𝕜)) :
    E [⋀^Fin (k + l)]→ₗ[𝕜] 𝕜 :=
by
  classical
  let wedge_tensor :
      E [⋀^Fin k ⊕ Fin l]→ₗ[𝕜] (TensorProduct 𝕜 𝕜 𝕜) :=
    AlternatingMap.domCoprod' (ιa := Fin k) (ιb := Fin l)
      (R' := 𝕜) (Mᵢ := E) (N₁ := 𝕜) (N₂ := 𝕜) t
  let wedge_scalar : E [⋀^Fin k ⊕ Fin l]→ₗ[𝕜] 𝕜 :=
    (LinearMap.mul' 𝕜 𝕜).compAlternatingMap wedge_tensor
  exact wedge_scalar.domDomCongr finSumFinEquiv

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
@[simp]
theorem wedgeAlternatingTensor_add {k l : ℕ}
    (t₁ t₂ :
      TensorProduct 𝕜 (E [⋀^Fin k]→ₗ[𝕜] 𝕜) (E [⋀^Fin l]→ₗ[𝕜] 𝕜)) :
    wedgeAlternatingTensor (𝕜 := 𝕜) (E := E) (k := k) (l := l) (t₁ + t₂) =
      wedgeAlternatingTensor (𝕜 := 𝕜) (E := E) (k := k) (l := l) t₁ +
        wedgeAlternatingTensor (𝕜 := 𝕜) (E := E) (k := k) (l := l) t₂ := by
  classical
  ext v
  simp [wedgeAlternatingTensor, map_add]

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
@[simp]
theorem wedgeAlternatingTensor_smul {k l : ℕ} (c : 𝕜)
    (t :
      TensorProduct 𝕜 (E [⋀^Fin k]→ₗ[𝕜] 𝕜) (E [⋀^Fin l]→ₗ[𝕜] 𝕜)) :
    wedgeAlternatingTensor (𝕜 := 𝕜) (E := E) (k := k) (l := l) (c • t) =
      c • wedgeAlternatingTensor (𝕜 := 𝕜) (E := E) (k := k) (l := l) t := by
  classical
  ext v
  simp [wedgeAlternatingTensor, map_smul, LinearMap.compAlternatingMap_smul,
    AlternatingMap.domDomCongr_smul]

noncomputable def wedgeAlternating {k l : ℕ}
    (ω : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k))
    (η : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l)) :
    E [⋀^Fin (k + l)]→ₗ[𝕜] 𝕜 :=
by
  classical
  exact wedgeAlternatingTensor (𝕜 := 𝕜) (E := E) (k := k) (l := l)
    (ω.toAlternatingMap ⊗ₜ[𝕜] η.toAlternatingMap)

noncomputable def wedge {k l : ℕ}
    (ω : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k))
    (η : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l)) :
    ContinuousAlternatingMap 𝕜 E 𝕜 (Fin (k + l)) :=
by
  classical
  let wedge_reindex : E [⋀^Fin (k + l)]→ₗ[𝕜] 𝕜 := wedgeAlternating (𝕜 := 𝕜) (E := E) ω η
  have h_ex :
      ∃ C : ℝ, ∀ v : Fin (k + l) → E, ‖wedge_reindex v‖ ≤ C * ∏ i, ‖v i‖ :=
    AlternatingMap.exists_bound_fin_dim (𝕜 := 𝕜) (E := E) (F := 𝕜) (ι := Fin (k + l))
      wedge_reindex
  let C : ℝ := Classical.choose h_ex
  have hC : ∀ v : Fin (k + l) → E, ‖wedge_reindex v‖ ≤ C * ∏ i, ‖v i‖ :=
    Classical.choose_spec h_ex
  exact wedge_reindex.mkContinuous C hC

@[simp] theorem wedge_apply {k l : ℕ}
    (ω : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k))
    (η : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l))
    (v : Fin (k + l) → E) :
    (wedge (𝕜 := 𝕜) (E := E) ω η) v =
      (wedgeAlternating (𝕜 := 𝕜) (E := E) ω η) v := by
  simp [wedge]

theorem wedge_add_left {k l : ℕ}
    (ω₁ ω₂ : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k))
    (η : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l)) :
    wedge (𝕜 := 𝕜) (E := E) (ω₁ + ω₂) η =
      wedge (𝕜 := 𝕜) (E := E) ω₁ η + wedge (𝕜 := 𝕜) (E := E) ω₂ η := by
  ext v
  simp [wedge_apply, wedgeAlternating, TensorProduct.add_tmul]

theorem wedge_add_right {k l : ℕ}
    (ω : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k))
    (η₁ η₂ : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l)) :
    wedge (𝕜 := 𝕜) (E := E) ω (η₁ + η₂) =
      wedge (𝕜 := 𝕜) (E := E) ω η₁ + wedge (𝕜 := 𝕜) (E := E) ω η₂ := by
  ext v
  simp [wedge_apply, wedgeAlternating, TensorProduct.tmul_add]

theorem wedge_smul_left {k l : ℕ} (c : 𝕜)
    (ω : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k))
    (η : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l)) :
    wedge (𝕜 := 𝕜) (E := E) (c • ω) η = c • wedge (𝕜 := 𝕜) (E := E) ω η := by
  ext v
  have htensor :
      ((c • ω.toAlternatingMap) ⊗ₜ[𝕜] η.toAlternatingMap) =
        c • (ω.toAlternatingMap ⊗ₜ[𝕜] η.toAlternatingMap) := by
      simp [TensorProduct.smul_tmul']
  simp [wedge_apply, wedgeAlternating, wedgeAlternatingTensor, htensor, map_smul,
    LinearMap.compAlternatingMap_smul, AlternatingMap.domDomCongr_smul]

theorem wedge_smul_right {k l : ℕ} (c : 𝕜)
    (ω : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k))
    (η : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l)) :
    wedge (𝕜 := 𝕜) (E := E) ω (c • η) = c • wedge (𝕜 := 𝕜) (E := E) ω η := by
  ext v
  have htensor :
      (ω.toAlternatingMap ⊗ₜ[𝕜] (c • η.toAlternatingMap)) =
        c • (ω.toAlternatingMap ⊗ₜ[𝕜] η.toAlternatingMap) := by
    have : c • (ω.toAlternatingMap ⊗ₜ[𝕜] η.toAlternatingMap) =
        (c • ω.toAlternatingMap) ⊗ₜ[𝕜] η.toAlternatingMap := by
      simp [TensorProduct.smul_tmul']
    have hmove :
        (c • ω.toAlternatingMap) ⊗ₜ[𝕜] η.toAlternatingMap =
          ω.toAlternatingMap ⊗ₜ[𝕜] (c • η.toAlternatingMap) := by
      simp [TensorProduct.smul_tmul (R := 𝕜) (R' := 𝕜) (M := (E [⋀^Fin k]→ₗ[𝕜] 𝕜))
        (N := (E [⋀^Fin l]→ₗ[𝕜] 𝕜)) c ω.toAlternatingMap η.toAlternatingMap]
    calc
      ω.toAlternatingMap ⊗ₜ[𝕜] (c • η.toAlternatingMap)
          = (c • ω.toAlternatingMap) ⊗ₜ[𝕜] η.toAlternatingMap := by
              simp [hmove]
      _ = c • (ω.toAlternatingMap ⊗ₜ[𝕜] η.toAlternatingMap) := by
              simp [this.symm]
  simp [wedge_apply, wedgeAlternating, wedgeAlternatingTensor, htensor, map_smul,
    LinearMap.compAlternatingMap_smul, AlternatingMap.domDomCongr_smul]

/-- Wedge product as a bundled bilinear continuous linear map. -/
noncomputable def wedgeCLM_alt (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] (k l : ℕ) :
    (ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k)) →L[𝕜]
      (ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l) →L[𝕜]
        ContinuousAlternatingMap 𝕜 E 𝕜 (Fin (k + l))) :=
  LinearMap.toContinuousLinearMap (𝕜 := 𝕜) (E := (ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k)))
    (F' := ((ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l)) →L[𝕜]
      (ContinuousAlternatingMap 𝕜 E 𝕜 (Fin (k + l))))) <|
  { toFun := fun ω =>
      LinearMap.toContinuousLinearMap (𝕜 := 𝕜) (E := (ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l)))
        (F' := (ContinuousAlternatingMap 𝕜 E 𝕜 (Fin (k + l)))) <|
      { toFun := fun η => wedge ω η
        map_add' := fun a b => wedge_add_right ω a b
        map_smul' := fun c a => wedge_smul_right c ω a }
    map_add' := fun a b => by ext η v; simp [wedge_add_left]
    map_smul' := fun c a => by ext η v; simp [wedge_smul_left] }

/-- The wedge product of continuous alternating maps is jointly continuous.

**Proof strategy**: `wedgeCLM_alt 𝕜 E k l` is a continuous bilinear map (curried form).
The function `(ω, η) ↦ wedge ω η = (wedgeCLM_alt ω) η` is therefore continuous as the
composition of:
1. `(ω, η) ↦ (wedgeCLM_alt ω, η)` which is continuous (f.continuous ∘ fst, snd)
2. `(g, η) ↦ g η` which is continuous by `isBoundedBilinearMap_apply.continuous`

The formal proof requires the `IsBoundedBilinearMap` structure for the uncurried wedge. -/
theorem continuous_wedge {k l : ℕ} :
    Continuous fun p :
        (ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k) ×
          ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l)) =>
        wedge (𝕜 := 𝕜) (E := E) p.1 p.2 := by
  classical
  let f := wedgeCLM_alt 𝕜 E k l
  show Continuous fun p : _ × _ => (f p.1) p.2
  -- The uncurried wedge is continuous because:
  -- - f : CAM k →L CAM l →L CAM (k+l) is a CLM (curried bilinear map)
  -- - The function (ω, η) ↦ (f ω) η is the uncurried application
  -- - isBoundedBilinearMap_apply shows (g, x) ↦ g x is continuous (CLM evaluation)
  -- Compose with (f ∘ fst, snd) : Prod → CLM × CAM to get our result
  let CAMk := ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k)
  let CAMl := ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l)
  let CAMkl := ContinuousAlternatingMap 𝕜 E 𝕜 (Fin (k + l))
  have h1 : Continuous (fun p : CAMk × CAMl => ((f p.1 : CAMl →L[𝕜] CAMkl), p.2)) :=
    (f.continuous.comp continuous_fst).prodMk continuous_snd
  exact (isBoundedBilinearMap_apply (𝕜 := 𝕜) (E := CAMl) (F := CAMkl)).continuous.comp h1

/-! ### Wedge with 0-forms (scalar multiplication)

When one of the forms is a 0-form (i.e., a constant scalar), the wedge product
reduces to scalar multiplication. This is the key identity for proving
that the unit 0-form acts as the identity for the cup product.

## Classical Pillar: Exterior Algebra Unit Laws

The wedge product with 0-forms (scalars) satisfies the expected unit laws from
exterior algebra. These are axiomatized as they require detailed shuffle arguments
on the `domCoprod` construction that are not yet available in Mathlib.

**Mathematical justification**:
- A 0-form on `Fin 0` takes no tangent vectors, so it's just a scalar `c : 𝕜`.
- For any l-form η and vectors v₁, ..., vₗ:
  `(c ∧ η)(v₁, ..., vₗ) = c · η(v₁, ..., vₗ)`

This follows from the definition of `domCoprod` where the sum over (0,l)-shuffles
has exactly one term (the identity), and the empty alternating map contributes
just its scalar value.

Reference: [Warner, "Foundations of Differentiable Manifolds and Lie Groups", Prop. 2.14] -/

/-! ### Helper lemmas for shuffle quotients

When one of the index types is empty (Fin 0), the shuffle quotient is trivial
(has exactly one element), making the sum collapse to a single term. -/

private lemma sumCongrHom_surj_empty_left {l : ℕ} :
    Function.Surjective (Equiv.Perm.sumCongrHom (Fin 0) (Fin l)) := by
  intro σ
  have h_pres : ∀ i : Fin l, ∃ j : Fin l, σ (Sum.inr i) = Sum.inr j := by
    intro i
    rcases σ (Sum.inr i) with ⟨x⟩ | ⟨j⟩
    · exact (IsEmpty.false x).elim
    · exact ⟨j, rfl⟩
  let q_fun : Fin l → Fin l := fun i => (h_pres i).choose
  have hq : ∀ i, σ (Sum.inr i) = Sum.inr (q_fun i) := fun i => (h_pres i).choose_spec
  have q_inj : Function.Injective q_fun := by
    intros i j hij
    have : σ (Sum.inr i) = σ (Sum.inr j) := by simp [hq, hij]
    exact Sum.inr_injective (σ.injective this)
  have q_surj : Function.Surjective q_fun := by
    intro j
    obtain ⟨x, hx⟩ := σ.surjective (Sum.inr j)
    rcases x with ⟨y⟩ | ⟨i⟩
    · exact (IsEmpty.false y).elim
    · use i
      have h1 : σ (Sum.inr i) = (Sum.inr j : Fin 0 ⊕ Fin l) := hx
      have h2 : σ (Sum.inr i) = (Sum.inr (q_fun i) : Fin 0 ⊕ Fin l) := hq i
      exact Sum.inr_injective (by rw [← h2, h1])
  let q : Equiv.Perm (Fin l) := Equiv.ofBijective q_fun ⟨q_inj, q_surj⟩
  use (1, q)
  ext x
  rcases x with ⟨y⟩ | ⟨i⟩
  · exact (IsEmpty.false y).elim
  · simp only [Equiv.Perm.sumCongrHom_apply, Equiv.Perm.sumCongr_apply, Sum.map_inr]
    exact (hq i).symm

private instance subsingleton_modSumCongr_empty_left {l : ℕ} :
    Subsingleton (Equiv.Perm.ModSumCongr (Fin 0) (Fin l)) := by
  constructor
  intros σ₁ σ₂
  induction σ₁ using Quotient.inductionOn' with
  | h s₁ =>
    induction σ₂ using Quotient.inductionOn' with
    | h s₂ =>
      apply Quotient.sound'
      rw [QuotientGroup.leftRel_apply]
      obtain ⟨pq, hpq⟩ := sumCongrHom_surj_empty_left (s₁⁻¹ * s₂)
      exact ⟨pq, hpq⟩

private lemma sumCongrHom_surj_empty_right {k : ℕ} :
    Function.Surjective (Equiv.Perm.sumCongrHom (Fin k) (Fin 0)) := by
  intro σ
  have h_pres : ∀ i : Fin k, ∃ j : Fin k, σ (Sum.inl i) = Sum.inl j := by
    intro i
    rcases σ (Sum.inl i) with ⟨j⟩ | ⟨x⟩
    · exact ⟨j, rfl⟩
    · exact (IsEmpty.false x).elim
  let p_fun : Fin k → Fin k := fun i => (h_pres i).choose
  have hp : ∀ i, σ (Sum.inl i) = Sum.inl (p_fun i) := fun i => (h_pres i).choose_spec
  have p_inj : Function.Injective p_fun := by
    intros i j hij
    have : σ (Sum.inl i) = σ (Sum.inl j) := by simp [hp, hij]
    exact Sum.inl_injective (σ.injective this)
  have p_surj : Function.Surjective p_fun := by
    intro j
    obtain ⟨x, hx⟩ := σ.surjective (Sum.inl j)
    rcases x with ⟨i⟩ | ⟨y⟩
    · use i
      have h1 : σ (Sum.inl i) = (Sum.inl j : Fin k ⊕ Fin 0) := hx
      have h2 : σ (Sum.inl i) = (Sum.inl (p_fun i) : Fin k ⊕ Fin 0) := hp i
      exact Sum.inl_injective (by rw [← h2, h1])
    · exact (IsEmpty.false y).elim
  let p : Equiv.Perm (Fin k) := Equiv.ofBijective p_fun ⟨p_inj, p_surj⟩
  use (p, 1)
  ext x
  rcases x with ⟨i⟩ | ⟨y⟩
  · simp only [Equiv.Perm.sumCongrHom_apply, Equiv.Perm.sumCongr_apply, Sum.map_inl]
    exact (hp i).symm
  · exact (IsEmpty.false y).elim

private instance subsingleton_modSumCongr_empty_right {k : ℕ} :
    Subsingleton (Equiv.Perm.ModSumCongr (Fin k) (Fin 0)) := by
  constructor
  intros σ₁ σ₂
  induction σ₁ using Quotient.inductionOn' with
  | h s₁ =>
    induction σ₂ using Quotient.inductionOn' with
    | h s₂ =>
      apply Quotient.sound'
      rw [QuotientGroup.leftRel_apply]
      obtain ⟨pq, hpq⟩ := sumCongrHom_surj_empty_right (s₁⁻¹ * s₂)
      exact ⟨pq, hpq⟩

private lemma sum_subsingleton {α : Type*} [Fintype α] [Subsingleton α] {M : Type*} [AddCommMonoid M]
    (f : α → M) (a : α) : ∑ x : α, f x = f a := by
  have h : ∀ x : α, x = a := fun x => Subsingleton.elim x a
  simp only [Finset.sum_eq_single a (fun b _ hb => absurd (h b) hb)
             (fun ha => absurd (Finset.mem_univ a) ha)]

private lemma finSumFinEquiv_inr_eq_finCongr {l : ℕ} (i : Fin l) :
    (finSumFinEquiv (Sum.inr i) : Fin (0 + l)) = finCongr (Nat.zero_add l).symm i := by
  simp only [finSumFinEquiv_apply_right, finCongr_apply]
  apply Fin.ext
  simp only [Fin.val_natAdd, Fin.val_cast]
  omega

private lemma finSumFinEquiv_inl_eq_finCongr {k : ℕ} (i : Fin k) :
    (finSumFinEquiv (Sum.inl i) : Fin (k + 0)) = finCongr (Nat.add_zero k).symm i := by
  simp only [finSumFinEquiv_apply_left, finCongr_apply]
  apply Fin.ext
  simp only [Fin.val_castAdd, Fin.val_cast]

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
@[simp]
private lemma constOfIsEmpty_toMultilinearMap_apply (c : 𝕜) (u : Fin 0 → E) :
    (constOfIsEmpty 𝕜 E (Fin 0) c).toMultilinearMap u = c := rfl

/-! ### Main wedge identity theorems -/

/-- **Theorem**: Wedge of a constant 0-form with an l-form is scalar multiplication.

A 0-form on `Fin 0` is just a scalar value. When we wedge it with an l-form,
the result is the l-form scaled by that scalar (with index type `Fin (0 + l) ≃ Fin l`).

This theorem encodes the standard exterior algebra identity: `1 ∧ η = η`. -/
theorem wedge_constOfIsEmpty_left {l : ℕ} (c : 𝕜)
    (η : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l)) :
    wedge (𝕜 := 𝕜) (E := E) (ContinuousAlternatingMap.constOfIsEmpty 𝕜 E (ι := Fin 0) c) η =
      (c • η).domDomCongr (finCongr (Nat.zero_add l).symm) := by
  classical
  ext v
  simp only [wedge_apply, wedgeAlternating, wedgeAlternatingTensor]
  simp only [domDomCongr_apply, smul_apply]
  simp only [AlternatingMap.domDomCongr_apply, LinearMap.compAlternatingMap_apply,
             AlternatingMap.domCoprod'_apply, AlternatingMap.domCoprod_apply,
             MultilinearMap.sum_apply]
  let σ₀ : Equiv.Perm.ModSumCongr (Fin 0) (Fin l) := ⟦1⟧
  rw [sum_subsingleton _ σ₀]
  simp only [AlternatingMap.domCoprod.summand]
  conv_lhs => rw [show σ₀ = ⟦1⟧ from rfl]
  simp only [Quotient.liftOn'_mk'', MultilinearMap.domDomCongr_apply,
             MultilinearMap.domCoprod_apply, Equiv.Perm.sign_one, one_smul,
             LinearMap.mul'_apply, Equiv.Perm.coe_one, id_eq, Function.comp_apply]
  have h_inputs : (fun i₂ => v (finSumFinEquiv (Sum.inr i₂))) = (v ∘ finCongr (Nat.zero_add l).symm) := by
    funext i
    simp only [Function.comp_apply]
    congr 1
    exact finSumFinEquiv_inr_eq_finCongr i
  simp only [h_inputs]
  rfl

/-- **Theorem**: Wedge of an l-form with a constant 0-form is scalar multiplication.

This is the right-handed version of the scalar identity: `η ∧ 1 = η`.
Combined with wedge_constOfIsEmpty_left, these give the unit laws for the cup product. -/
theorem wedge_constOfIsEmpty_right {k : ℕ} (c : 𝕜)
    (ω : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k)) :
    wedge (𝕜 := 𝕜) (E := E) ω (ContinuousAlternatingMap.constOfIsEmpty 𝕜 E (ι := Fin 0) c) =
      (c • ω).domDomCongr (finCongr (Nat.add_zero k).symm) := by
  classical
  ext v
  simp only [wedge_apply, wedgeAlternating, wedgeAlternatingTensor]
  simp only [domDomCongr_apply, smul_apply]
  simp only [AlternatingMap.domDomCongr_apply, LinearMap.compAlternatingMap_apply,
             AlternatingMap.domCoprod'_apply, AlternatingMap.domCoprod_apply,
             MultilinearMap.sum_apply]
  let σ₀ : Equiv.Perm.ModSumCongr (Fin k) (Fin 0) := ⟦1⟧
  rw [sum_subsingleton _ σ₀]
  simp only [AlternatingMap.domCoprod.summand]
  conv_lhs => rw [show σ₀ = ⟦1⟧ from rfl]
  simp only [Quotient.liftOn'_mk'', MultilinearMap.domDomCongr_apply,
             MultilinearMap.domCoprod_apply, Equiv.Perm.sign_one, one_smul,
             LinearMap.mul'_apply, Equiv.Perm.coe_one, id_eq, Function.comp_apply]
  have h_left : (fun i₁ => v (finSumFinEquiv (Sum.inl i₁))) = (v ∘ finCongr (Nat.add_zero k).symm) := by
    funext i
    simp only [Function.comp_apply, finSumFinEquiv_inl_eq_finCongr]
  have h_const : (constOfIsEmpty 𝕜 E (Fin 0) c).toMultilinearMap
                 (fun i₂ => v (finSumFinEquiv (Sum.inr i₂))) = c := rfl
  rw [h_left, h_const, smul_eq_mul, mul_comm]
  rfl

/-! ### Wedge associativity

The wedge product is associative up to index reordering. This is the key property
needed for the cohomology ring structure.

## Classical Pillar: Exterior Algebra Associativity

**Mathematical justification**:
The wedge product on differential forms is associative:
`(ω ∧ η) ∧ θ = ω ∧ (η ∧ θ)`

This follows from:
1. Tensor product associativity in the underlying algebra
2. The shuffle product formula for domCoprod being associative
3. The definition of wedge as domCoprod composed with multiplication

The proof requires matching shuffle permutations across different index decompositions,
which is a substantial combinatorial argument not yet formalized in Mathlib.

Reference: [Bott & Tu, "Differential Forms in Algebraic Topology", §1.2]
           [Warner, "Foundations of Differentiable Manifolds and Lie Groups", Prop. 2.14] -/

/-!
NOTE: wedge_assoc was archived to archive/Hodge/Analytic/WedgeAssoc.lean because it is
NOT on the proof track of hodge_conjecture'.
-/

end ContinuousAlternatingMap

end
