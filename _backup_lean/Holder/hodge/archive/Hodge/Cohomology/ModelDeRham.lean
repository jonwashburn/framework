import Hodge.Analytic.ModelDeRham
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Module.Alternating.Uncurry.Fin

/-!
Model-space de Rham cohomology (Stage 2 groundwork).

This file builds a **Mathlib-backed** exterior derivative on *smooth* (C^∞) model-space forms
on `ℂⁿ`, and defines the associated de Rham cohomology (as a quotient of closed forms by exact
forms) at the level of additive groups.

This is intentionally kept on the model space `E = EuclideanSpace ℂ (Fin n)`; transporting this
to manifolds is Stage 2/3 of the broader migration plan.
-/

noncomputable section

open Classical

set_option autoImplicit false

namespace Hodge

/-! ## Smooth model-space forms -/

-- We use `ContDiff ℂ (⊤ : ℕ∞)` = `C^∞` (not the `ω`/analytic top case of `WithTop ℕ∞`).
abbrev ModelSmoothForm (n k : ℕ) : Type :=
  { ω : ModelForm n k // ContDiff ℂ (⊤ : ℕ∞) ω }

namespace ModelSmoothForm

variable {n k : ℕ}

@[simp] lemma coe_mk (ω : ModelForm n k) (h : ContDiff ℂ (⊤ : ℕ∞) ω) :
    ((⟨ω, h⟩ : ModelSmoothForm n k) : ModelForm n k) = ω := rfl

instance (k : ℕ) : CoeFun (ModelSmoothForm n k) (fun _ => ModelForm n k) where
  coe ω := ω.1

@[ext] lemma ext {k : ℕ} {ω₁ ω₂ : ModelSmoothForm n k} (h : (ω₁ : ModelForm n k) = ω₂) : ω₁ = ω₂ := by
  cases ω₁; cases ω₂; cases h; rfl

instance (k : ℕ) : Zero (ModelSmoothForm n k) := ⟨⟨0, contDiff_const⟩⟩
instance (k : ℕ) : Add (ModelSmoothForm n k) :=
  ⟨fun ω η => ⟨ω + η, ω.2.add η.2⟩⟩
instance (k : ℕ) : Neg (ModelSmoothForm n k) :=
  ⟨fun ω => ⟨-ω, ω.2.neg⟩⟩
instance (k : ℕ) : Sub (ModelSmoothForm n k) :=
  ⟨fun ω η => ⟨ω - η, ω.2.sub η.2⟩⟩
instance (k : ℕ) : SMul ℂ (ModelSmoothForm n k) :=
  ⟨fun c ω => ⟨c • (ω : ModelForm n k), contDiff_const.smul ω.2⟩⟩

@[simp] lemma zero_coe (k : ℕ) : ((0 : ModelSmoothForm n k) : ModelForm n k) = 0 := rfl
@[simp] lemma add_coe (k : ℕ) (ω η : ModelSmoothForm n k) : ((ω + η : ModelSmoothForm n k) : ModelForm n k) = (ω : ModelForm n k) + η := rfl
@[simp] lemma neg_coe (k : ℕ) (ω : ModelSmoothForm n k) : ((-ω : ModelSmoothForm n k) : ModelForm n k) = -(ω : ModelForm n k) := rfl
@[simp] lemma sub_coe (k : ℕ) (ω η : ModelSmoothForm n k) : ((ω - η : ModelSmoothForm n k) : ModelForm n k) = (ω : ModelForm n k) - η := rfl
@[simp] lemma smul_coe (k : ℕ) (c : ℂ) (ω : ModelSmoothForm n k) :
    ((c • ω : ModelSmoothForm n k) : ModelForm n k) = c • (ω : ModelForm n k) := rfl

instance instAddCommGroup (k : ℕ) : AddCommGroup (ModelSmoothForm n k) where
  add_assoc := by
    intro a b c
    apply Subtype.ext
    funext x
    simp [add_assoc]
  zero_add := by
    intro a
    apply Subtype.ext
    funext x
    simp
  add_zero := by
    intro a
    apply Subtype.ext
    funext x
    simp
  add_comm := by
    intro a b
    apply Subtype.ext
    funext x
    simp [add_comm]
  neg_add_cancel := by
    intro a
    apply Subtype.ext
    funext x
    simp
  nsmul := nsmulRec
  zsmul := zsmulRec
  sub_eq_add_neg := by
    intro a b
    apply Subtype.ext
    funext x
    simp [sub_eq_add_neg]

instance instModule (k : ℕ) : Module ℂ (ModelSmoothForm n k) where
  add_smul := by
    intro a b ω
    apply Subtype.ext
    funext x
    simpa using (_root_.add_smul a b ((ω : ModelForm n k) x))
  smul_add := by
    intro a ω η
    apply Subtype.ext
    funext x
    simpa using (_root_.smul_add a ((ω : ModelForm n k) x) ((η : ModelForm n k) x))
  mul_smul := by
    intro a b ω
    apply Subtype.ext
    funext x
    simpa using (SemigroupAction.mul_smul a b ((ω : ModelForm n k) x))
  one_smul := by
    intro ω
    apply Subtype.ext
    funext x
    simpa using (_root_.one_smul ℂ ((ω : ModelForm n k) x))
  smul_zero := by
    intro a
    apply Subtype.ext
    funext x
    -- reduce to the pointwise statement on `ContinuousAlternatingMap`
    ext v
    simp
  zero_smul := by
    intro ω
    apply Subtype.ext
    funext x
    ext v
    simp

/-! ## Exterior derivative on smooth model-space forms -/

noncomputable def d {k : ℕ} (ω : ModelSmoothForm n k) : ModelSmoothForm n (k + 1) :=
  ⟨ModelForm.d (n := n) (k := k) (ω : ModelForm n k), by
    -- `ModelForm.d ω = fun x => extDeriv ω x = alternatizeUncurryFinCLM _ _ _ (fderiv _ ω x)`.
    -- Smoothness follows from smoothness of `fderiv` and smoothness of a continuous linear map.
    have hfd : ContDiff ℂ (⊤ : ℕ∞) (fderiv ℂ (ω : ModelForm n k)) := by
      -- `C^∞` implies the derivative is `C^∞`.
      -- Use the general "derivative is one order less" lemma (∞ stays ∞).
      simpa using (ω.2.fderiv_right (m := (⊤ : ℕ∞)) (by simpa))
    -- Apply a continuous linear map to `fderiv`.
    -- `extDeriv ω x = ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℂ ω x)`
    -- and `alternatizeUncurryFin` is a continuous linear map (`alternatizeUncurryFinCLM`).
    simpa [ModelForm.d, Hodge.ModelForm.d, extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin] using
      ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℂ (ModelSpace n) ℂ (n := k)).contDiff.comp hfd)⟩

@[simp] lemma d_coe {k : ℕ} (ω : ModelSmoothForm n k) :
    ((d (n := n) ω : ModelSmoothForm n (k + 1)) : ModelForm n (k + 1)) = ModelForm.d (n := n) (k := k) (ω : ModelForm n k) := rfl

theorem d_add {k : ℕ} (ω₁ ω₂ : ModelSmoothForm n k) : d (n := n) (ω₁ + ω₂) = d ω₁ + d ω₂ := by
  apply Subtype.ext
  funext x
  -- Use Mathlib's extDeriv_add (requires differentiability, provided by C^∞).
  have h1 : DifferentiableAt ℂ (ω₁ : ModelForm n k) x :=
    (ω₁.2.contDiffAt.differentiableAt (by simp))
  have h2 : DifferentiableAt ℂ (ω₂ : ModelForm n k) x :=
    (ω₂.2.contDiffAt.differentiableAt (by simp))
  simpa [d, ModelForm.d] using (extDeriv_add (x := x) h1 h2)

theorem d_smul {k : ℕ} (c : ℂ) (ω : ModelSmoothForm n k) : d (n := n) (c • ω) = c • d ω := by
  apply Subtype.ext
  funext x
  simpa [d, ModelForm.d] using (extDeriv_smul (x := x) (c := c) (ω := (ω : ModelForm n k)))

@[simp] theorem d_zero (k : ℕ) : d (n := n) (0 : ModelSmoothForm n k) = 0 := by
  -- use ℂ-linearity with `c = 0`
  simpa [zero_smul, smul_zero] using (d_smul (n := n) (k := k) (0 : ℂ) (0 : ModelSmoothForm n k))

theorem d_neg {k : ℕ} (ω : ModelSmoothForm n k) : d (n := n) (-ω) = -d ω := by
  -- `-ω = (-1) • ω`
  simpa [neg_one_smul] using (d_smul (n := n) (k := k) (-1 : ℂ) ω)

theorem d_sq {k : ℕ} (ω : ModelSmoothForm n k) : d (n := n) (d ω) = 0 := by
  apply Subtype.ext
  -- Use Mathlib's `extDeriv_extDeriv` for `C^∞` functions.
  have h0 : extDeriv (extDeriv (ω : ModelForm n k)) = 0 := by
    have hr : minSmoothness ℂ 2 ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
      -- `minSmoothness ℂ 2 = 2`
      simpa using (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
    simpa using (extDeriv_extDeriv (ω := (ω : ModelForm n k)) (h := ω.2) (hr := hr))
  -- Unfold our `d`.
  simpa [d, ModelForm.d] using h0

/-! ## Closed / exact forms and cohomology (additive) -/

def IsClosed {k : ℕ} (ω : ModelSmoothForm n k) : Prop := d (n := n) ω = 0

def IsExact {k : ℕ} (ω : ModelSmoothForm n k) : Prop :=
  match k with
  | 0 => ω = 0
  | k' + 1 => ∃ η : ModelSmoothForm n k', d (n := n) η = ω

structure ClosedForm (n : ℕ) (k : ℕ) where
  val : ModelSmoothForm n k
  property : IsClosed (n := n) val

namespace ClosedForm

variable {k : ℕ}

instance : Coe (ClosedForm n k) (ModelSmoothForm n k) := ⟨ClosedForm.val⟩

instance : Add (ClosedForm n k) :=
  ⟨fun ω η =>
    ⟨ω.val + η.val, by
      -- d(ω+η)=dω+dη=0
      unfold IsClosed at *
      calc
        d (n := n) (ω.val + η.val) = d (n := n) ω.val + d (n := n) η.val := d_add (n := n) ω.val η.val
        _ = 0 + 0 := by rw [ω.property, η.property]
        _ = 0 := by simp⟩⟩

instance : Neg (ClosedForm n k) :=
  ⟨fun ω =>
    ⟨-ω.val, by
      unfold IsClosed at *
      -- d(-ω)= -dω
      calc
        d (n := n) (-ω.val) = -d (n := n) ω.val := by simpa using d_neg (n := n) (ω := ω.val)
        _ = -0 := by rw [ω.property]
        _ = 0 := by simp⟩⟩

instance : Zero (ClosedForm n k) :=
  ⟨⟨0, by
    unfold IsClosed
    -- d(0)=0
    simpa using d_zero (n := n) (k := k)⟩⟩

end ClosedForm

/-! The cohomology quotient. -/

def Cohomologous {k : ℕ} (ω₁ ω₂ : ClosedForm n k) : Prop :=
  IsExact (n := n) (ω₁.val - ω₂.val)

theorem cohomologous_refl {k : ℕ} (ω : ClosedForm n k) : Cohomologous (n := n) ω ω := by
  unfold Cohomologous IsExact
  cases k with
  | zero =>
    -- `IsExact` in degree 0 is `ω = 0`
    simp
  | succ k' =>
    refine ⟨0, ?_⟩
    -- d(0) = 0 and ω - ω = 0
    simpa [d_zero, sub_self]

theorem cohomologous_symm {k : ℕ} {ω η : ClosedForm n k} :
    Cohomologous (n := n) ω η → Cohomologous (n := n) η ω := by
  intro h
  unfold Cohomologous at *
  cases k with
  | zero =>
    -- exactness is equality to zero in degree 0
    -- from `ω - η = 0` get `ω = η`, hence `η - ω = 0`
    have hEq : (ω.val : ModelSmoothForm n 0) = η.val := by
      exact sub_eq_zero.mp h
    simpa [IsExact, hEq]
  | succ k' =>
    rcases h with ⟨β, hβ⟩
    refine ⟨-β, ?_⟩
    -- d(-β) = -dβ = -(ω-η) = (η-ω)
    simpa [d_neg (n := n) (ω := β), hβ, neg_sub]

theorem cohomologous_trans {k : ℕ} {ω η θ : ClosedForm n k} :
    Cohomologous (n := n) ω η → Cohomologous (n := n) η θ → Cohomologous (n := n) ω θ := by
  intro h1 h2
  unfold Cohomologous at *
  cases k with
  | zero =>
    -- exactness is equality to zero
    have hEq1 : (ω.val : ModelSmoothForm n 0) = η.val := sub_eq_zero.mp h1
    have hEq2 : (η.val : ModelSmoothForm n 0) = θ.val := sub_eq_zero.mp h2
    have hEq : (ω.val : ModelSmoothForm n 0) = θ.val := hEq1.trans hEq2
    simpa [IsExact, hEq]
  | succ k' =>
    rcases h1 with ⟨α, hα⟩
    rcases h2 with ⟨β, hβ⟩
    refine ⟨α + β, ?_⟩
    -- d(α+β)=dα+dβ=(ω-η)+(η-θ)=(ω-θ)
    simpa [d_add, hα, hβ, sub_add_sub_cancel]

instance DeRhamSetoid (k : ℕ) : Setoid (ClosedForm n k) where
  r := Cohomologous (n := n)
  iseqv := ⟨cohomologous_refl (n := n), cohomologous_symm (n := n), cohomologous_trans (n := n)⟩

def DeRhamCohomology (n : ℕ) (k : ℕ) : Type :=
  Quotient (DeRhamSetoid (n := n) k)

end ModelSmoothForm

end Hodge
