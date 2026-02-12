import Hodge.Analytic.Forms
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Module.Basic

/-!
# De Rham Cohomology

This file defines de Rham cohomology for complex manifolds and establishes
its algebraic structure (ring structure via wedge product).

## Main Definitions

* `Cohomologous`: The equivalence relation for de Rham cohomology
* `DeRhamSetoid`: The setoid structure for cohomology classes
* `DeRhamCohomologyClass`: The quotient type H^k(X) = Z^k(X) / B^k(X)
* `KahlerManifold`: Type class for compact Kähler manifolds

## Main Results

* Cohomology classes form a ℂ-module
* Wedge product descends to a ring structure on cohomology
* Kähler manifolds have additional structure (Kähler form ω)

## Mathematical Background

De Rham cohomology is defined as:
  H^k(X) = {closed k-forms} / {exact k-forms}

where a form is closed if dω = 0 and exact if ω = dη for some η.
-/

noncomputable section

open Classical

set_option autoImplicit false

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [ProjectiveComplexManifold n X]

namespace Hodge

/-- The equivalence relation for de Rham cohomology. -/
def Cohomologous {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    (ω₁ ω₂ : ClosedForm n X k) : Prop := IsExact (ω₁.val - ω₂.val)

/-- Exactness implies closedness (d² = 0). -/
theorem isFormClosed_of_isExact {k : ℕ} {ω : SmoothForm n X k} : IsExact ω → IsFormClosed ω := by
  cases k with
  | zero => intro h; unfold IsFormClosed; rw [h, smoothExtDeriv_zero]
  | succ k' =>
    rintro ⟨η, rfl⟩
    unfold IsFormClosed
    exact smoothExtDeriv_extDeriv η

theorem cohomologous_refl {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    (ω : ClosedForm n X k) : Cohomologous ω ω := by
  unfold Cohomologous IsExact
  simp only [sub_self]
  cases k with | zero => rfl | succ k' => exact ⟨0, smoothExtDeriv_zero⟩

theorem cohomologous_symm {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    {ω η : ClosedForm n X k} : Cohomologous ω η → Cohomologous η ω := by
  intro h
  unfold Cohomologous at *
  -- h : IsExact (ω.val - η.val), goal: IsExact (η.val - ω.val)
  -- η.val - ω.val = -(ω.val - η.val)
  have heq : η.val - ω.val = -(ω.val - η.val) := (neg_sub ω.val η.val).symm
  rw [heq]
  -- Show IsExact (-α) from IsExact α
  unfold IsExact at *
  cases k with
  | zero =>
    -- h : ω.val - η.val = 0, goal: -(ω.val - η.val) = 0
    simp [h]
  | succ k' =>
    -- h : ∃ β, dβ = (ω.val - η.val), goal: ∃ β, dβ = -(ω.val - η.val)
    obtain ⟨β, hβ⟩ := h
    use -β
    rw [smoothExtDeriv_neg, hβ]

theorem cohomologous_trans {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    {ω η θ : ClosedForm n X k} : Cohomologous ω η → Cohomologous η θ → Cohomologous ω θ := by
  intro h1 h2
  unfold Cohomologous at *
  -- h1: IsExact (ω.val - η.val), h2: IsExact (η.val - θ.val)
  -- goal: IsExact (ω.val - θ.val)
  -- ω.val - θ.val = (ω.val - η.val) + (η.val - θ.val)
  have heq : ω.val - θ.val = (ω.val - η.val) + (η.val - θ.val) := by
    simp only [sub_add_sub_cancel]
  rw [heq]
  -- Show IsExact (α + β) from IsExact α and IsExact β
  unfold IsExact at *
  cases k with
  | zero =>
    -- h1 : ω.val - η.val = 0, h2 : η.val - θ.val = 0
    simp [h1, h2]
  | succ k' =>
    -- h1 : ∃ α, dα = (ω.val - η.val), h2 : ∃ β, dβ = (η.val - θ.val)
    obtain ⟨α, hα⟩ := h1
    obtain ⟨β, hβ⟩ := h2
    use α + β
    rw [smoothExtDeriv_add, hα, hβ]

instance DeRhamSetoid (n k : ℕ) (X : Type u) [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] : Setoid (ClosedForm n X k) where
  r := Cohomologous
  iseqv := ⟨cohomologous_refl, cohomologous_symm, cohomologous_trans⟩

/-- De Rham cohomology group of degree k. -/
def DeRhamCohomologyClass (n : ℕ) (X : Type u) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] : Type u := Quotient (DeRhamSetoid n k X)

def ofForm {k : ℕ} (ω : SmoothForm n X k) (h : IsFormClosed ω) : DeRhamCohomologyClass n X k := Quotient.mk _ ⟨ω, h⟩
notation "⟦" ω "," h "⟧" => ofForm ω h

-- `ofForm` is insensitive to the particular closedness proof (proof irrelevance).
theorem ofForm_proof_irrel {k : ℕ} (ω : SmoothForm n X k) (h₁ h₂ : IsFormClosed ω) :
    ⟦ω, h₁⟧ = ⟦ω, h₂⟧ := by
  apply Quotient.sound
  exact cohomologous_refl ⟨ω, h₁⟩

instance (k : ℕ) : Zero (DeRhamCohomologyClass n X k) := ⟨⟦0, isFormClosed_zero⟧⟩

/-- Casting zero across cohomology degrees gives zero.
    This holds because both zeros are quotients of the zero closed form,
    and the cast preserves the quotient structure. -/
theorem DeRhamCohomologyClass.cast_zero {k₁ k₂ : ℕ} (h : k₁ = k₂) :
    h ▸ (0 : DeRhamCohomologyClass n X k₁) = (0 : DeRhamCohomologyClass n X k₂) := by
  subst h
  rfl

/-- Casting a closedness proof along a degree equality.
    This is a small helper for working with degree-indexed forms. -/
theorem IsFormClosed_castForm {k₁ k₂ : ℕ} (h : k₁ = k₂) (ω : SmoothForm n X k₁)
    (hω : IsFormClosed ω) : IsFormClosed (castForm (n := n) (X := X) h ω) := by
  subst h
  simpa [castForm] using hω

/-- `ofForm` is compatible with degree casts: casting the cohomology class equals
the class of the casted representative form. -/
theorem DeRhamCohomologyClass.cast_ofForm {k₁ k₂ : ℕ} (h : k₁ = k₂)
    (ω : SmoothForm n X k₁) (hω : IsFormClosed ω) :
    h ▸ (⟦ω, hω⟧ : DeRhamCohomologyClass n X k₁) =
      (⟦castForm (n := n) (X := X) h ω, IsFormClosed_castForm (n := n) (X := X) h ω hω⟧ :
        DeRhamCohomologyClass n X k₂) := by
  subst h
  rfl

/-! ### Well-definedness axioms -/

theorem cohomologous_add {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    (ω₁ ω₁' ω₂ ω₂' : ClosedForm n X k) (h1 : ω₁ ≈ ω₁') (h2 : ω₂ ≈ ω₂') : (ω₁ + ω₂) ≈ (ω₁' + ω₂') := by
  -- Unfold the Setoid relation to Cohomologous
  show Cohomologous (ω₁ + ω₂) (ω₁' + ω₂')
  unfold Cohomologous
  have h1' : Cohomologous ω₁ ω₁' := h1
  have h2' : Cohomologous ω₂ ω₂' := h2
  unfold Cohomologous at h1' h2'
  -- (ω₁ + ω₂).val - (ω₁' + ω₂').val = (ω₁.val - ω₁'.val) + (ω₂.val - ω₂'.val)
  have hval_add : ∀ (f g : ClosedForm n X k), (f + g).val = f.val + g.val := fun _ _ => rfl
  have heq : (ω₁ + ω₂).val - (ω₁' + ω₂').val = (ω₁.val - ω₁'.val) + (ω₂.val - ω₂'.val) := by
    simp only [hval_add]
    ext x v
    simp only [SmoothForm.add_apply, SmoothForm.sub_apply]
    abel
  rw [heq]
  unfold IsExact at *
  cases k with
  | zero => simp [h1', h2']
  | succ k' =>
    obtain ⟨α, hα⟩ := h1'
    obtain ⟨β, hβ⟩ := h2'
    use α + β
    rw [smoothExtDeriv_add, hα, hβ]

theorem cohomologous_neg {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    (ω ω' : ClosedForm n X k) (h : ω ≈ ω') : (-ω) ≈ (-ω') := by
  show Cohomologous (-ω) (-ω')
  unfold Cohomologous
  have h' : Cohomologous ω ω' := h
  unfold Cohomologous at h'
  -- (-ω).val - (-ω').val = -ω.val - (-ω'.val) = -ω.val + ω'.val = -(ω.val - ω'.val)
  have hval_neg : ∀ (f : ClosedForm n X k), (-f).val = -f.val := fun _ => rfl
  have heq : (-ω).val - (-ω').val = -(ω.val - ω'.val) := by
    simp only [hval_neg]
    ext x v
    simp only [SmoothForm.sub_apply, SmoothForm.neg_apply]
    -- Goal: -a - (-b) = b - a   =>   -a + b = b - a, which is true
    abel
  rw [heq]
  unfold IsExact at *
  cases k with
  | zero => simp [h']
  | succ k' =>
    obtain ⟨β, hβ⟩ := h'
    use -β
    rw [smoothExtDeriv_neg, hβ]

theorem cohomologous_smul {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    (c : ℂ) (ω ω' : ClosedForm n X k) (h : ω ≈ ω') :
    (⟨c • ω.val, isFormClosed_smul ω.property⟩ : ClosedForm n X k) ≈ ⟨c • ω'.val, isFormClosed_smul ω'.property⟩ := by
  show Cohomologous _ _
  unfold Cohomologous
  have h' : Cohomologous ω ω' := h
  unfold Cohomologous at h'
  -- (c • ω.val) - (c • ω'.val) = c • (ω.val - ω'.val)
  have heq : (c • ω.val) - (c • ω'.val) = c • (ω.val - ω'.val) := (smul_sub c ω.val ω'.val).symm
  rw [heq]
  unfold IsExact at *
  cases k with
  | zero =>
    -- h' : ω.val - ω'.val = 0, goal: c • (ω.val - ω'.val) = 0
    simp [h']
  | succ k' =>
    -- h' : ∃ β, dβ = (ω.val - ω'.val), goal: ∃ β, dβ = c • (ω.val - ω'.val)
    obtain ⟨β, hβ⟩ := h'
    use c • β
    -- Need: d(c • β) = c • dβ, but smoothExtDeriv is ℂ-linear (from extDerivLinearMap)
    rw [← hβ]
    -- smoothExtDeriv is defined as extDerivLinearMap, which is ℂ-linear
    simp only [smoothExtDeriv, map_smul]

/-! ### Helper theorems for cohomologous_wedge -/

-- Helper: casting zero gives zero (via Eq.rec)
omit [ProjectiveComplexManifold n X] in
@[simp] private theorem eqRec_zero {k k' : ℕ} (h : k = k') :
    h ▸ (0 : SmoothForm n X k) = (0 : SmoothForm n X k') := by subst h; rfl

-- Helper: exterior derivative commutes with castForm
omit [ProjectiveComplexManifold n X] in
@[simp] private theorem smoothExtDeriv_castForm {k k' : ℕ} (h : k = k') (ω : SmoothForm n X k) :
    smoothExtDeriv (castForm (n := n) (X := X) h ω) =
      castForm (congrArg (· + 1) h) (smoothExtDeriv ω) := by subst h; rfl

-- Helper: exterior derivative commutes with Eq.rec (▸)
omit [ProjectiveComplexManifold n X] in
@[simp] private theorem smoothExtDeriv_eqRec {k k' : ℕ} (h : k = k') (ω : SmoothForm n X k) :
    smoothExtDeriv (h ▸ ω) = (congrArg (· + 1) h) ▸ smoothExtDeriv ω := by subst h; rfl

-- Helper: castForm commutes with scalar multiplication
omit [ProjectiveComplexManifold n X] in
@[simp] private theorem castForm_smul {k k' : ℕ} (h : k = k') (c : ℂ) (ω : SmoothForm n X k) :
    castForm h (c • ω) = c • castForm h ω := by subst h; rfl

-- Helper: nested castForm resolves when degrees match
omit [ProjectiveComplexManifold n X] in
@[simp] private theorem castForm_castForm {k k' k'' : ℕ} (h : k = k') (h' : k' = k'') (ω : SmoothForm n X k) :
    castForm h' (castForm h ω) = castForm (h.trans h') ω := by subst h; subst h'; rfl

-- Helper: castForm with equality proof resolves to the form when degrees are the same type
omit [ProjectiveComplexManifold n X] in
private theorem castForm_eq_of_proof_irrel {k : ℕ} (h : k = k) (ω : SmoothForm n X k) :
    castForm h ω = ω := by rfl

-- Helper: Eq.rec with reflexive equality is identity
omit [ProjectiveComplexManifold n X] in
@[simp] private theorem eqRec_trans {k k' k'' : ℕ} (h : k = k') (h' : k' = k'') (ω : SmoothForm n X k) :
    h' ▸ (h ▸ ω) = (h.trans h') ▸ ω := by subst h; subst h'; rfl

-- Helper: Eq.rec with proof that types match is identity
omit [ProjectiveComplexManifold n X] in
@[simp] private theorem eqRec_refl' {k : ℕ} (h : k = k) (ω : SmoothForm n X k) :
    h ▸ ω = ω := by rfl

omit [ProjectiveComplexManifold n X] in
private theorem smoothWedge_sub_left' {k l : ℕ} (ω₁ ω₂ : SmoothForm n X k) (η : SmoothForm n X l) :
    (ω₁ - ω₂) ⋏ η = (ω₁ ⋏ η) - (ω₂ ⋏ η) := by
  rw [sub_eq_add_neg, smoothWedge_add_left]
  have h : (-ω₂) ⋏ η = -(ω₂ ⋏ η) := by
    rw [show (-ω₂) = (-1 : ℂ) • ω₂ by simp, smoothWedge_smul_left, neg_one_smul]
  rw [h, ← sub_eq_add_neg]

omit [ProjectiveComplexManifold n X] in
private theorem smoothWedge_sub_right' {k l : ℕ} (ω : SmoothForm n X k) (η₁ η₂ : SmoothForm n X l) :
    ω ⋏ (η₁ - η₂) = (ω ⋏ η₁) - (ω ⋏ η₂) := by
  rw [sub_eq_add_neg, smoothWedge_add_right]
  have h : ω ⋏ (-η₂) = -(ω ⋏ η₂) := by
    rw [show (-η₂) = (-1 : ℂ) • η₂ by simp, smoothWedge_smul_right, neg_one_smul]
  rw [h, ← sub_eq_add_neg]

omit [ProjectiveComplexManifold n X] in
private theorem wedge_sub_decompose' {k l : ℕ}
    (ω₁ ω₁' : SmoothForm n X k) (ω₂ ω₂' : SmoothForm n X l) :
    (ω₁ ⋏ ω₂) - (ω₁' ⋏ ω₂') = ((ω₁ - ω₁') ⋏ ω₂) + (ω₁' ⋏ (ω₂ - ω₂')) := by
  rw [smoothWedge_sub_left', smoothWedge_sub_right']
  simp only [sub_add_sub_cancel]

/-- **Wedge Product Respects Cohomology** (PROVED).

    If ω₁ ~ ω₁' and ω₂ ~ ω₂' (cohomologous forms), then ω₁ ∧ ω₂ ~ ω₁' ∧ ω₂'.

    The proof uses the Leibniz rule: d(α ∧ β) = dα ∧ β + (-1)^deg(α) α ∧ dβ.

    ## References

    - [Bott-Tu, "Differential Forms in Algebraic Topology", Ch. 1]
    - [Warner, "Foundations of Differentiable Manifolds and Lie Groups", Ch. 5] -/
theorem cohomologous_wedge {n k l : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    (ω₁ ω₁' : ClosedForm n X k) (ω₂ ω₂' : ClosedForm n X l) (h1 : ω₁ ≈ ω₁') (h2 : ω₂ ≈ ω₂') :
    (⟨ω₁.val ⋏ ω₂.val, isFormClosed_wedge _ _ ω₁.property ω₂.property⟩ : ClosedForm n X (k + l)) ≈
      ⟨ω₁'.val ⋏ ω₂'.val, isFormClosed_wedge _ _ ω₁'.property ω₂'.property⟩ := by
  show Cohomologous _ _
  unfold Cohomologous
  rw [wedge_sub_decompose']
  have h1' : Cohomologous ω₁ ω₁' := h1
  have h2' : Cohomologous ω₂ ω₂' := h2
  unfold Cohomologous at h1' h2'
  unfold IsExact at *
  cases k with
  | zero =>
    have hω1_eq : ω₁.val = ω₁'.val := sub_eq_zero.mp h1'
    simp only [hω1_eq, sub_self, smoothWedge_zero_left, zero_add]
    cases l with
    | zero =>
      have hω2_eq : ω₂.val = ω₂'.val := sub_eq_zero.mp h2'
      simp only [hω2_eq, sub_self, wedge_zero]
    | succ l' =>
      obtain ⟨η₂, hη₂⟩ := h2'
      refine ⟨ω₁'.val ⋏ η₂, ?_⟩
      have hLeibniz := smoothExtDeriv_wedge ω₁'.val η₂
      have hClosed : smoothExtDeriv ω₁'.val = 0 := ω₁'.property
      simp only [hLeibniz, hClosed, smoothWedge_zero_left, eqRec_zero, castForm_zero,
                 zero_add, pow_zero, one_smul, ← hη₂, castForm]
  | succ k' =>
    obtain ⟨η₁, hη₁⟩ := h1'
    cases l with
    | zero =>
      have hω2_eq : ω₂.val = ω₂'.val := sub_eq_zero.mp h2'
      simp only [hω2_eq, sub_self, wedge_zero, add_zero]
      refine ⟨η₁ ⋏ ω₂'.val, ?_⟩
      have hLeibniz := smoothExtDeriv_wedge η₁ ω₂'.val
      have hClosed : smoothExtDeriv ω₂'.val = 0 := ω₂'.property
      simp only [hLeibniz, hClosed, wedge_zero, smul_zero, add_zero, ← hη₁, castForm,
                 eqRec_trans, eqRec_refl']
    | succ l' =>
      obtain ⟨η₂, hη₂⟩ := h2'
      let β₁ : SmoothForm n X (k' + (l' + 1)) := η₁ ⋏ ω₂.val
      let β₂ : SmoothForm n X ((k' + 1) + l') := ω₁'.val ⋏ η₂
      have hdeg : k' + (l' + 1) = (k' + 1) + l' := by omega
      refine ⟨castForm hdeg β₁ + (-1 : ℂ)^(k' + 1) • β₂, ?_⟩
      have hLeibniz1 := smoothExtDeriv_wedge η₁ ω₂.val
      have hClosed2 : smoothExtDeriv ω₂.val = 0 := ω₂.property
      have hLeibniz2 := smoothExtDeriv_wedge ω₁'.val η₂
      have hClosed1' : smoothExtDeriv ω₁'.val = 0 := ω₁'.property
      have hSign : ((-1 : ℂ)^(k' + 1)) * ((-1 : ℂ)^(k' + 1)) = 1 := by
        rw [← pow_add, show k' + 1 + (k' + 1) = 2 * (k' + 1) by ring,
            pow_mul, neg_one_sq, one_pow]
      -- Complete proof using Leibniz rule
      dsimp only [β₁, β₂]
      rw [smoothExtDeriv_add, smoothExtDeriv_smul, smoothExtDeriv_castForm]
      rw [hLeibniz1, hClosed2, wedge_zero, smul_zero]
      simp only [castForm_zero, add_zero]
      rw [hLeibniz2, hClosed1', smoothWedge_zero_left]
      simp only [castForm_zero, zero_add]
      simp only [smul_comm ((-1 : ℂ)^(k' + 1)) (castForm _ _), castForm_smul, smul_smul, hSign, one_smul]
      rw [← hη₁, ← hη₂]
      simp only [eqRec_trans, eqRec_refl', castForm]


/-! ### Algebraic Instances -/

/-- Addition on de Rham cohomology classes, defined via Quotient.lift₂ -/
instance instAddDeRhamCohomologyClass (k : ℕ) : Add (DeRhamCohomologyClass n X k) where
  add := Quotient.lift₂ (fun a b => ⟦a.val + b.val, isFormClosed_add a.property b.property⟧)
    (fun a₁ b₁ a₂ b₂ h1 h2 => Quotient.sound (cohomologous_add a₁ a₂ b₁ b₂ h1 h2))

/-- Negation on de Rham cohomology classes, defined via Quotient.lift -/
instance instNegDeRhamCohomologyClass (k : ℕ) : Neg (DeRhamCohomologyClass n X k) where
  neg := Quotient.lift (fun a => ⟦-a.val, isFormClosed_neg a.property⟧)
    (fun a b h => Quotient.sound (cohomologous_neg a b h))

/-- Subtraction on de Rham cohomology classes -/
instance instSubDeRhamCohomologyClass (k : ℕ) : Sub (DeRhamCohomologyClass n X k) where
  sub a b := a + (-b)

/-- Scalar multiplication by ℂ on de Rham cohomology classes -/
instance instSMulComplexDeRhamCohomologyClass (k : ℕ) : SMul ℂ (DeRhamCohomologyClass n X k) where
  smul c := Quotient.lift (fun a => ⟦c • a.val, isFormClosed_smul a.property⟧)
    (fun a b h => Quotient.sound (cohomologous_smul c a b h))

/-- Scalar multiplication by ℝ on de Rham cohomology classes -/
instance instSMulRealDeRhamCohomologyClass (k : ℕ) : SMul ℝ (DeRhamCohomologyClass n X k) where
  smul r := Quotient.lift (fun a => ⟦r • a.val, isFormClosed_smul_real a.property⟧)
    (fun a b h => by
      apply Quotient.sound
      -- r • a ≈ r • b follows from c • a ≈ c • b with c = (r : ℂ)
      have hc : (⟨(r : ℂ) • a.val, isFormClosed_smul a.property⟩ : ClosedForm n X k) ≈
                ⟨(r : ℂ) • b.val, isFormClosed_smul b.property⟩ := cohomologous_smul (r : ℂ) a b h
      convert hc using 1)

/-- AddCommGroup structure on de Rham cohomology classes -/
instance instAddCommGroupDeRhamCohomologyClass (k : ℕ) : AddCommGroup (DeRhamCohomologyClass n X k) where
  add_assoc := by
    intro a b c
    induction a using Quotient.ind
    induction b using Quotient.ind
    induction c using Quotient.ind
    apply Quotient.sound
    show Cohomologous _ _
    simp only [add_assoc]
    exact cohomologous_refl _
  zero_add := by
    intro a
    induction a using Quotient.ind
    apply Quotient.sound
    show Cohomologous _ _
    simp only [zero_add]
    exact cohomologous_refl _
  add_zero := by
    intro a
    induction a using Quotient.ind
    apply Quotient.sound
    show Cohomologous _ _
    simp only [add_zero]
    exact cohomologous_refl _
  add_comm := by
    intro a b
    induction a using Quotient.ind
    induction b using Quotient.ind
    apply Quotient.sound
    show Cohomologous _ _
    simp only [add_comm]
    exact cohomologous_refl _
  neg_add_cancel := by
    intro a
    induction a using Quotient.ind
    apply Quotient.sound
    show Cohomologous _ _
    simp only [neg_add_cancel]
    exact cohomologous_refl _
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- Module structure over ℂ on de Rham cohomology classes -/
instance instModuleComplexDeRhamCohomologyClass (k : ℕ) : Module ℂ (DeRhamCohomologyClass n X k) where
  one_smul := by
    intro a
    induction a using Quotient.ind
    apply Quotient.sound
    show Cohomologous _ _
    simp only [one_smul]
    exact cohomologous_refl _
  mul_smul := by
    intro r s a
    induction a using Quotient.ind
    apply Quotient.sound
    show Cohomologous _ _
    simp only [mul_smul]
    exact cohomologous_refl _
  smul_zero := by
    intro r
    apply Quotient.sound
    show Cohomologous _ _
    simp only [smul_zero]
    exact cohomologous_refl _
  smul_add := by
    intro r a b
    induction a using Quotient.ind
    induction b using Quotient.ind
    apply Quotient.sound
    show Cohomologous _ _
    simp only [smul_add]
    exact cohomologous_refl _
  add_smul := by
    intro r s a
    induction a using Quotient.ind
    apply Quotient.sound
    show Cohomologous _ _
    simp only [add_smul]
    exact cohomologous_refl _
  zero_smul := by
    intro a
    induction a using Quotient.ind
    apply Quotient.sound
    show Cohomologous _ _
    simp only [zero_smul]
    exact cohomologous_refl _

/-- Scalar multiplication by ℚ on de Rham cohomology classes -/
instance instSMulRationalDeRhamCohomologyClass (k : ℕ) : SMul ℚ (DeRhamCohomologyClass n X k) where
  smul q a := (q : ℂ) • a

-- Compatibility: rational scalar multiplication equals real scalar multiplication.
theorem smul_rat_eq_smul_real {k : ℕ} (q : ℚ) (η : DeRhamCohomologyClass n X k) :
    q • η = (q : ℝ) • η := by
  induction η using Quotient.ind
  apply Quotient.sound
  show Cohomologous _ _
  -- (q : ℂ) • a = (q : ℝ) • a since (q : ℂ) = ((q : ℝ) : ℂ)
  have h : (q : ℂ) = ((q : ℝ) : ℂ) := by norm_cast
  simp only [h]
  exact cohomologous_refl _

/-- Multiplication on de Rham cohomology classes (cup product via wedge) -/
instance instHMulDeRhamCohomologyClass (k l : ℕ) :
    HMul (DeRhamCohomologyClass n X k) (DeRhamCohomologyClass n X l)
      (DeRhamCohomologyClass n X (k + l)) where
  hMul := Quotient.lift₂ (fun a b => ⟦a.val ⋏ b.val, isFormClosed_wedge _ _ a.property b.property⟧)
    (fun a₁ b₁ a₂ b₂ h1 h2 => Quotient.sound (cohomologous_wedge a₁ a₂ b₁ b₂ h1 h2))

/-! ### Algebraic laws for cup product -/

theorem mul_add {k l : ℕ} (a : DeRhamCohomologyClass n X k) (b c : DeRhamCohomologyClass n X l) :
    a * (b + c) = a * b + a * c := by
  -- work on representatives
  refine Quotient.inductionOn₃ a b c ?_
  intro a b c
  -- reduce equality of quotients to cohomology of representatives
  apply Quotient.sound
  show Cohomologous _ _
  unfold Cohomologous
  have hEq : a.val ⋏ (b.val + c.val) = (a.val ⋏ b.val) + (a.val ⋏ c.val) := by
    simp [smoothWedge_add_right]
  -- The difference is 0 by algebraic equality, hence exact.
  simp [hEq]
  exact isExact_zero

theorem add_mul {k l : ℕ} (a b : DeRhamCohomologyClass n X k) (c : DeRhamCohomologyClass n X l) :
    (a + b) * c = a * c + b * c := by
  refine Quotient.inductionOn₃ a b c ?_
  intro a b c
  apply Quotient.sound
  show Cohomologous _ _
  unfold Cohomologous
  have hEq : (a.val + b.val) ⋏ c.val = (a.val ⋏ c.val) + (b.val ⋏ c.val) := by
    simp [smoothWedge_add_left]
  -- The difference is 0 by algebraic equality, hence exact.
  simp [hEq]
  exact isExact_zero

theorem mul_smul {k l : ℕ} (a : DeRhamCohomologyClass n X k) (r : ℂ) (b : DeRhamCohomologyClass n X l) :
    a * (r • b) = r • (a * b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro a b
  apply Quotient.sound
  show Cohomologous _ _
  unfold Cohomologous
  have hEq : a.val ⋏ (r • b.val) = r • (a.val ⋏ b.val) := by
    simp [smoothWedge_smul_right]
  -- The difference is 0 by algebraic equality, hence exact.
  simp [hEq]
  exact isExact_zero

theorem smul_mul {k l : ℕ} (r : ℂ) (a : DeRhamCohomologyClass n X k) (b : DeRhamCohomologyClass n X l) :
    (r • a) * b = r • (a * b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro a b
  apply Quotient.sound
  show Cohomologous _ _
  unfold Cohomologous
  have hEq : (r • a.val) ⋏ b.val = r • (a.val ⋏ b.val) := by
    simp [smoothWedge_smul_left]
  -- The difference is 0 by algebraic equality, hence exact.
  simp [hEq]
  exact isExact_zero

theorem zero_mul {k l : ℕ} (a : DeRhamCohomologyClass n X l) :
    (0 : DeRhamCohomologyClass n X k) * a = 0 := by
  refine Quotient.inductionOn a ?_
  intro a
  apply Quotient.sound
  show Cohomologous _ _
  unfold Cohomologous
  have hEq : (0 : SmoothForm n X k) ⋏ a.val = 0 := by
    simp [smoothWedge_zero_left]
  -- exactness: difference is exact
  simp [hEq]
  exact isExact_zero

theorem mul_zero {k l : ℕ} (a : DeRhamCohomologyClass n X k) :
    a * (0 : DeRhamCohomologyClass n X l) = 0 := by
  refine Quotient.inductionOn a ?_
  intro a
  apply Quotient.sound
  show Cohomologous _ _
  unfold Cohomologous
  have hEq : a.val ⋏ (0 : SmoothForm n X l) = 0 := by
    simp [smoothWedge_zero_right]
  -- exactness: difference is exact
  simp [hEq]
  exact isExact_zero

/-! ### Associativity of Cup Product

The cup product on cohomology is associative: `(a * b) * c = a * (b * c)`.

**Degree arithmetic**: The multiplication `HMul` has types:
- `(a * b) * c : DeRhamCohomologyClass n X ((k + l) + m)`
- `a * (b * c) : DeRhamCohomologyClass n X (k + (l + m))`

Since `(k + l) + m = k + (l + m)` propositionally but not definitionally,
we need to cast one side. -/

/-!
NOTE: mul_assoc was archived with wedge_assoc because it depends on smoothWedge_assoc,
which is NOT on the proof track of hodge_conjecture'.
-/

/-! ### Unit Element for Cup Product

The unit form in H⁰(X) satisfies `1 * a = a` and `a * 1 = a` (up to degree casts).

**Note**: `unitForm` is defined as the constant-`1` 0-form in `Hodge/Analytic/Forms.lean`.
These unit theorems are proved using the current form-level infrastructure
(`smoothWedge_unitForm_left/right`) and then transported to cohomology via the quotient. -/

/-- The unit cohomology class in H⁰(X). -/
def unitClass : DeRhamCohomologyClass n X 0 := ⟦unitForm, isFormClosed_unitForm⟧

/-- Left multiplication by unit: `unitClass * a = a` (up to degree cast).

The unit cohomology class acts as a left identity for the cup product.
The cast is induced by `0 + k = k`.

This follows from the form-level identity `unitForm ⋏ ω = ω`
(via `smoothWedge_unitForm_left`). -/
theorem one_mul {k : ℕ} (a : DeRhamCohomologyClass n X k) :
    (unitClass (n := n) (X := X)) * a = (Nat.zero_add k).symm ▸ a := by
  refine Quotient.inductionOn a ?_
  rintro ⟨ω, hω⟩
  -- Compute the product on representatives.
  simp [unitClass, instHMulDeRhamCohomologyClass, ofForm]
  -- Rewrite the degree cast on the RHS into an `ofForm` of the casted form.
  change
    (⟦unitForm ⋏ ω, ?_⟧ : DeRhamCohomologyClass n X (0 + k)) =
      (Nat.zero_add k).symm ▸ (⟦ω, hω⟧ : DeRhamCohomologyClass n X k)
  rw [DeRhamCohomologyClass.cast_ofForm (n := n) (X := X)
        (h := (Nat.zero_add k).symm)
        (ω := ω)]
  apply Quotient.sound
  show Cohomologous _ _
  unfold Cohomologous
  have hEq : unitForm ⋏ ω = castForm (n := n) (X := X) (Nat.zero_add k).symm ω := by
    simpa using (smoothWedge_unitForm_left (n := n) (X := X) (k := k) ω)
  simp [hEq]
  exact isExact_zero

/-- Right multiplication by unit: `a * unitClass = a` (up to degree cast).

The unit cohomology class acts as a right identity for the cup product.
The cast is induced by `k + 0 = k`.

This follows from the form-level identity `ω ⋏ unitForm = castForm _ ω`
(via `smoothWedge_unitForm_right`). -/
theorem mul_one {k : ℕ} (a : DeRhamCohomologyClass n X k) :
    a * (unitClass (n := n) (X := X)) = (Nat.add_zero k).symm ▸ a := by
  refine Quotient.inductionOn a ?_
  rintro ⟨ω, hω⟩
  -- Compute the product on representatives.
  simp [unitClass, instHMulDeRhamCohomologyClass, ofForm]
  -- Rewrite the degree cast on the RHS into an `ofForm` of the casted form.
  change
    (⟦ω ⋏ unitForm, ?_⟧ : DeRhamCohomologyClass n X (k + 0)) =
      (Nat.add_zero k).symm ▸ (⟦ω, hω⟧ : DeRhamCohomologyClass n X k)
  rw [DeRhamCohomologyClass.cast_ofForm (n := n) (X := X)
        (h := (Nat.add_zero k).symm)
        (ω := ω)]
  apply Quotient.sound
  show Cohomologous _ _
  unfold Cohomologous
  have hEq : ω ⋏ unitForm = castForm (n := n) (X := X) (Nat.add_zero k).symm ω := by
    simpa using (smoothWedge_unitForm_right (n := n) (X := X) (k := k) ω)
  simp [hEq]
  exact isExact_zero

/-! ## Rational Classes -/

/-- **Witness class for rational forms** (Comparison Isomorphism).

    A form ω is in this class when its de Rham cohomology class lies in the image
    of the comparison map H^k(X, ℚ) → H^k(X, ℂ).

    **Mathematical Background**:
    On a projective variety X, the comparison isomorphism identifies:
    - Singular cohomology H^k(X, ℂ) with de Rham cohomology H^k_dR(X, ℂ)
    - The rational lattice H^k(X, ℚ) ⊗ ℂ maps to rational de Rham classes

    This class serves as an axiomatized interface: specific forms (like the Kähler form)
    can be declared as witnesses without requiring the full comparison theory.

    Reference: [Voisin, "Hodge Theory and Complex Algebraic Geometry", Vol. I, Chapter 5]. -/
class IsRationalFormWitness (n : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] (k : ℕ) (ω : SmoothForm n X k) : Prop where
  /-- The form is closed (required for it to define a cohomology class). -/
  is_closed : IsFormClosed ω

/-- **Rational cohomology classes** (Hodge Theory).

    A de Rham cohomology class is rational if it lies in the ℚ-span of:
    1. The zero class (trivially rational)
    2. The unit class in H⁰ (represented by constant functions)
    3. Classes represented by forms with an `IsRationalFormWitness` instance
    4. Sums, rational scalar multiples, negations, and products of rational classes

    **Key change from previous definition**: The `of_witness` constructor allows
    non-zero rational classes to be declared axiomatically. This breaks the
    previous collapse where all rational classes were provably zero.

    Reference: [Griffiths-Harris, "Principles of Algebraic Geometry", 1978, Chapter 0]. -/
inductive isRationalClass {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [ProjectiveComplexManifold n X] :
    ∀ {k : ℕ}, DeRhamCohomologyClass n X k → Prop where
  | zero {k : ℕ} : isRationalClass (0 : DeRhamCohomologyClass n X k)
  | unit : isRationalClass unitClass  -- The unit (constant 1) is rational
  | of_witness {k : ℕ} (ω : SmoothForm n X k) [hw : IsRationalFormWitness n X k ω] :
      isRationalClass ⟦ω, hw.is_closed⟧
  | add {k : ℕ} {η₁ η₂ : DeRhamCohomologyClass n X k} :
      isRationalClass η₁ → isRationalClass η₂ → isRationalClass (η₁ + η₂)
  | smul_rat {k : ℕ} (q : ℚ) {η : DeRhamCohomologyClass n X k} :
      isRationalClass η → isRationalClass (q • η)
  | neg {k : ℕ} {η : DeRhamCohomologyClass n X k} :
      isRationalClass η → isRationalClass (-η)
  | mul {k l : ℕ} {η₁ : DeRhamCohomologyClass n X k} {η₂ : DeRhamCohomologyClass n X l} :
      isRationalClass η₁ → isRationalClass η₂ → isRationalClass (η₁ * η₂)

/-- `isRationalClass` is stable under degree casts. -/
theorem isRationalClass_cast {k₁ k₂ : ℕ} (h : k₁ = k₂) (η : DeRhamCohomologyClass n X k₁) :
    isRationalClass η → isRationalClass (h ▸ η) := by
  intro hη
  subst h
  simpa using hη

theorem isRationalClass_zero {k : ℕ} :
    isRationalClass (n := n) (X := X) (k := k) (0 : DeRhamCohomologyClass n X k) :=
  isRationalClass.zero

theorem isRationalClass_unit :
    isRationalClass (n := n) (X := X) unitClass :=
  isRationalClass.unit

/-- A form with an `IsRationalFormWitness` instance defines a rational cohomology class.
    This version allows providing an explicit closedness proof for flexibility. -/
theorem isRationalClass_of_witness {k : ℕ} (ω : SmoothForm n X k)
    [hw : IsRationalFormWitness n X k ω] (h_closed : IsFormClosed ω) :
    isRationalClass ⟦ω, h_closed⟧ := by
  have h : ⟦ω, h_closed⟧ = ⟦ω, hw.is_closed⟧ := ofForm_proof_irrel ω h_closed hw.is_closed
  rw [h]
  exact isRationalClass.of_witness ω

theorem isRationalClass_add {k : ℕ} (η₁ η₂ : DeRhamCohomologyClass n X k) :
    isRationalClass η₁ → isRationalClass η₂ → isRationalClass (η₁ + η₂) :=
  isRationalClass.add

theorem isRationalClass_smul_rat {k : ℕ} (q : ℚ) (η : DeRhamCohomologyClass n X k) :
    isRationalClass η → isRationalClass (q • η) :=
  isRationalClass.smul_rat q

theorem isRationalClass_neg {k : ℕ} (η : DeRhamCohomologyClass n X k) :
    isRationalClass η → isRationalClass (-η) :=
  isRationalClass.neg

-- isRationalClass_sub follows from add and neg
theorem isRationalClass_sub {k} (η₁ η₂ : DeRhamCohomologyClass n X k) : isRationalClass η₁ → isRationalClass η₂ → isRationalClass (η₁ - η₂) := by
  intro h1 h2
  -- η₁ - η₂ = η₁ + (-η₂)
  show isRationalClass (η₁ + (-η₂))
  exact isRationalClass.add h1 (isRationalClass.neg h2)

-- Rational classes form a subring (closed under cup product).
theorem isRationalClass_mul {k l} (η₁ : DeRhamCohomologyClass n X k) (η₂ : DeRhamCohomologyClass n X l) (h1 : isRationalClass η₁) (h2 : isRationalClass η₂) : isRationalClass (η₁ * η₂) := by
  exact isRationalClass.mul h1 h2

/-! ## Descent Properties -/

-- ofForm_add follows directly from the Quotient.lift₂ definition
theorem ofForm_add {k : ℕ} (ω η : SmoothForm n X k) (hω : IsFormClosed ω) (hη : IsFormClosed η) : ⟦ω + η, isFormClosed_add hω hη⟧ = ⟦ω, hω⟧ + ⟦η, hη⟧ := rfl

-- ofForm_smul follows directly from the Quotient.lift definition
theorem ofForm_smul {k : ℕ} (c : ℂ) (ω : SmoothForm n X k) (hω : IsFormClosed ω) : ⟦c • ω, isFormClosed_smul hω⟧ = c • ⟦ω, hω⟧ := rfl

-- ofForm_smul_real follows directly from the Quotient.lift definition
theorem ofForm_smul_real {k : ℕ} (r : ℝ) (ω : SmoothForm n X k) (hω : IsFormClosed ω) : ⟦r • ω, isFormClosed_smul_real hω⟧ = r • ⟦ω, hω⟧ := rfl

-- ofForm_sub follows from ofForm_add and ofForm_neg
theorem ofForm_sub {k : ℕ} (ω η : SmoothForm n X k) (hω : IsFormClosed ω) (hη : IsFormClosed η) : ⟦ω - η, isFormClosed_sub hω hη⟧ = ⟦ω, hω⟧ - ⟦η, hη⟧ := by
  show ⟦ω - η, _⟧ = ⟦ω, hω⟧ + (-⟦η, hη⟧)
  -- Need to show ⟦ω - η, _⟧ = ⟦ω, hω⟧ + ⟦-η, _⟧
  apply Quotient.sound
  show Cohomologous _ _
  simp only [sub_eq_add_neg]
  exact cohomologous_refl _

-- ofForm_wedge follows directly from the Quotient.lift₂ definition
theorem ofForm_wedge {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l) (hω : IsFormClosed ω) (hη : IsFormClosed η) : ⟦ω ⋏ η, isFormClosed_wedge ω η hω hη⟧ = ⟦ω, hω⟧ * ⟦η, hη⟧ := rfl

/-! ## (p,p) Forms -/

/-- **J-Invariance Property for (1,1)-Forms**

A 2-form ω on a complex manifold is of type (1,1) iff it is invariant under the almost
complex structure J: ω(Jv, Jw) = ω(v, w). On EuclideanSpace ℂ (Fin n), J acts as
multiplication by Complex.I on each coordinate.

This is the defining property that distinguishes (1,1)-forms from (2,0) or (0,2) forms. -/
def IsJInvariant2Form {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    (ω : SmoothForm n X 2) : Prop :=
  ∀ (x : X) (v w : TangentSpace (𝓒_complex n) x),
    ω.as_alternating x ![Complex.I • v, Complex.I • w] = ω.as_alternating x ![v, w]

/-- **Inductive characterization of (p,p)-forms**

A differential form is of type (p,p) if it can be built from:
1. The zero form (trivial)
2. The unit form (constant 1, type (0,0))
3. Any J-invariant 2-form (type (1,1)) - this includes the Kähler form
4. Sums, scalar multiples, and wedge products of (p,p)-forms

This inductive captures the algebraic structure of (p,p)-forms while providing
non-trivial base cases that prevent the degenerate "all forms = 0" situation. -/
inductive isPPForm' (n : ℕ) (X : Type u) [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] : (p : ℕ) → SmoothForm n X (2 * p) → Prop where
  | zero (p) : isPPForm' n X p 0
  | unitForm : isPPForm' n X 0 unitForm
  | jInvariant (ω : SmoothForm n X 2) (hJ : IsJInvariant2Form ω) :
      isPPForm' n X 1 ((Nat.two_mul 1).symm ▸ ω)
  | add {p ω η} : isPPForm' n X p ω → isPPForm' n X p η → isPPForm' n X p (ω + η)
  | smul {p} (c : ℂ) {ω} : isPPForm' n X p ω → isPPForm' n X p (c • ω)
  | wedge {p q} {ω : SmoothForm n X (2 * p)} {η : SmoothForm n X (2 * q)} :
      isPPForm' n X p ω → isPPForm' n X q η →
      isPPForm' n X (p + q) (castForm (by ring : 2 * p + 2 * q = 2 * (p + q)) (ω ⋏ η))

theorem isPPForm_zero {p} : isPPForm' n X p 0 := isPPForm'.zero p

/-- The unit form (constant 1) is a (0,0)-form. -/
theorem isPPForm_unitForm : isPPForm' n X 0 unitForm := isPPForm'.unitForm

/-- Any J-invariant 2-form is a (1,1)-form.

This is the key non-trivial base case that allows the Kähler form to be (1,1)
without degenerating to zero. -/
theorem isPPForm_of_JInvariant (ω : SmoothForm n X 2) (hJ : IsJInvariant2Form ω) :
    isPPForm' n X 1 ((Nat.two_mul 1).symm ▸ ω) :=
  isPPForm'.jInvariant ω hJ

theorem isPPForm_wedge {p q} {ω : SmoothForm n X (2 * p)} {η : SmoothForm n X (2 * q)}
    (hp : isPPForm' n X p ω) (hq : isPPForm' n X q η) :
    isPPForm' n X (p + q) (castForm (by ring : 2 * p + 2 * q = 2 * (p + q)) (ω ⋏ η)) :=
  isPPForm'.wedge hp hq

/-- A cohomology class is of type (p,p) if it has a (p,p) representative form.
    This is used in the statement of the Hard Lefschetz theorem on Hodge types. -/
def isPPClass (k : ℕ) (c : DeRhamCohomologyClass n X k) : Prop :=
  ∃ (p : ℕ) (hk : k = 2 * p) (η : SmoothForm n X k) (hc : IsFormClosed η),
    ⟦η, hc⟧ = c ∧ isPPForm' n X p (hk ▸ η)

/-! ## General Lefschetz Operators (parameterized by cohomology class) -/

/-- General Lefschetz operator defined by multiplication with a degree-2 cohomology class. -/
noncomputable def lefschetz_operator_of_class {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [ProjectiveComplexManifold n X]
    (ω : DeRhamCohomologyClass n X 2) (p : ℕ) :
    DeRhamCohomologyClass n X p →ₗ[ℂ] DeRhamCohomologyClass n X (p + 2) where
  toFun c := c * ω
  map_add' c₁ c₂ := add_mul c₁ c₂ ω
  map_smul' r c := by
    simp only [RingHom.id_apply]
    exact smul_mul r c ω

/-- General iterated Lefschetz map defined by multiplication with a degree-2 cohomology class. -/
def lefschetz_power_of_class {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [ProjectiveComplexManifold n X]
    (ω : DeRhamCohomologyClass n X 2) (p k : ℕ) :
    DeRhamCohomologyClass n X p →ₗ[ℂ] DeRhamCohomologyClass n X (p + 2 * k) :=
  match k with
  | 0 => LinearMap.id
  | k' + 1 =>
    let L := lefschetz_operator_of_class ω (p + 2 * k')
    let Lk := lefschetz_power_of_class ω p k'
    LinearMap.comp L Lk

/-! ## Kähler Manifold -/

/-!
### (Off-track) Classical Pillar: Hard Lefschetz Theorem

The **Hard Lefschetz Theorem** (Lefschetz, 1924) states that for a compact Kähler
manifold X of complex dimension n, the iterated Lefschetz operator
```
  L^k : H^{n-k}(X, ℂ) → H^{n+k}(X, ℂ)
```
defined by `L^k(α) = [ω]^k ∪ α` is an isomorphism.

**Status in this repository**: Hard Lefschetz is intentionally **not** a field of the
`KahlerManifold` structure on the main proof track. If you want to work with Hard Lefschetz
off-track, use the interface in:
- `Hodge/Kahler/Lefschetz/Sl2Representation.lean` (assumption packaged as `Hodge.HardLefschetzData`)
- `Hodge/Classical/Lefschetz.lean` (builds the inverse via `LinearEquiv.ofBijective`)

A full proof from first principles would require:
1. **Kähler identities**: `[Λ, d] = i∂̄*`, `[L, d*] = -i∂̄`
2. **Hodge decomposition**: H^k = ⊕_{p+q=k} H^{p,q}
3. **Primitive decomposition**: H^k = ⊕_r L^r(P^{k-2r})
4. **sl(2) representation theory**: L, Λ, H form an sl(2) representation

**Proof Path**: The complete proof would proceed as follows:
- Define the operators L (Lefschetz), Λ (dual Lefschetz), H (weight)
- Prove the Kähler identities using ∂, ∂̄, ⋆ operators
- Show that (L, Λ, H) satisfy sl(2) commutation relations
- Apply representation theory: highest weight vectors are primitive
- Conclude that L^k is an isomorphism by the sl(2) structure

**Estimated Effort**: 6-12 months for a complete formalization.

**Reference**: [Griffiths-Harris, "Principles of Algebraic Geometry", Ch. 0, §6-7]
             [Voisin, "Hodge Theory and Complex Algebraic Geometry I", Ch. 5-6]
-/

class KahlerManifold (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [ProjectiveComplexManifold n X] where
  omega_form : SmoothForm n X 2
  omega_closed : IsFormClosed omega_form
  /-- Positivity of the Kähler form: \(ω(v, Jv) > 0\) for all nonzero real tangent vectors.

  In this codebase’s model, the complex structure \(J\) is represented by multiplication by `Complex.I`
  on `TangentSpace (𝓒_complex n) x`. We record positivity as positivity of the real part of
  `ω(v, i•v)`. -/
  omega_positive :
    ∀ (x : X) (v : TangentSpace (𝓒_complex n) x), v ≠ 0 →
      0 < (omega_form.as_alternating x ![v, Complex.I • v]).re
  omega_is_pp : isPPForm' n X 1 omega_form
  /-- **Kähler form rationality witness** (Comparison Isomorphism).
      The Kähler form defines a rational cohomology class because it is the first
      Chern class of an ample line bundle on a projective variety.
      Reference: [Griffiths-Harris, 1978, Chapter 1]. -/
  omega_rational_witness : IsRationalFormWitness n X 2 omega_form
  omega_J_invariant : ∀ (x : X) (v w : TangentSpace (𝓒_complex n) x),
    omega_form.as_alternating x ![Complex.I • v, Complex.I • w] = omega_form.as_alternating x ![v, w]

/-!
══════════════════════════════════════════════════════════════════════════════════════════
**NOTE**: The Hard Lefschetz fields have been REMOVED from the `KahlerManifold` class.

The following three fields were previously here but are NOT on the proof track
for `hodge_conjecture'` and have been moved off-track.

- `lefschetz_bijective` : L^k is a bijection (Hard Lefschetz Theorem)
- `rational_lefschetz_iff` : L^k preserves rationality
- `pp_lefschetz_iff` : L^k preserves (p,p) type

**Why removed?**
These were "hidden axioms" in the type class that didn't appear in `#print axioms`
output, but represented assumptions about Kähler manifolds. Since they're not used
in the proof of `hodge_conjecture'`, removing them makes the proof track cleaner.

**Mathematical status**: The Hard Lefschetz Theorem IS a classical theorem
(Lefschetz 1924), but proving it requires significant infrastructure:
- Kähler identities
- Hodge decomposition
- sl(2) representation theory
- Primitive decomposition

If future work needs these, they can be restored from the archive.
══════════════════════════════════════════════════════════════════════════════════════════
-/

/-- **Kähler form is rational** (Derived from witness).
    This theorem extracts the rationality of the Kähler form's cohomology class
    from the `IsRationalFormWitness` instance in the `KahlerManifold` class.
    This replaces the former `omega_rational` field. -/
theorem KahlerManifold.omega_rational [K : KahlerManifold n X] :
    isRationalClass ⟦K.omega_form, K.omega_closed⟧ := by
  haveI : IsRationalFormWitness n X 2 K.omega_form := K.omega_rational_witness
  exact isRationalClass_of_witness K.omega_form K.omega_closed

/-! ## Lefschetz Operator -/

variable [KahlerManifold n X]

/-- **Lefschetz Operator L** (Kähler Geometry).
    L(η) = ω ∧ η where ω is the Kähler form. -/
noncomputable def lefschetzL {k : ℕ} (η : SmoothForm n X k) : SmoothForm n X (k + 2) :=
  (Nat.add_comm 2 k) ▸ (KahlerManifold.omega_form (n := n) (X := X) ⋏ η)

-- lefschetzL_add, lefschetzL_smul, lefschetzL_closed removed (unused)
-- NOTE: These lemmas are straightforward (they follow from `smoothWedge_add_*` / `smoothWedge_smul_*`)
-- but were removed as unused; reintroducing them requires a small amount of `Nat.add_comm` casting.

end Hodge

end
