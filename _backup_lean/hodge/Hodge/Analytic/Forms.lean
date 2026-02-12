import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Topology.Algebra.Support
import Hodge.Analytic.DomCoprod
import Hodge.Analytic.DomCoprodComplex
import Hodge.Analytic.FormType
import Hodge.Analytic.Advanced.ContMDiffForms
import Hodge.Analytic.Advanced.LeibnizRule
import Hodge.Basic

/-!
# Smooth Differential Forms

This file defines smooth differential forms on complex manifolds and provides
the core operations: exterior derivative, wedge product, and basic form algebra.

## Main Definitions

* `SmoothForm n X k`: Smooth k-forms on a complex n-dimensional manifold X
* `smoothExtDeriv`: The exterior derivative d : Ω^k → Ω^{k+1}
* `wedge` (notation `⋏`): Wedge product of forms
* `IsFormClosed`, `IsExact`: Closed and exact form predicates
* `ClosedForm`: The subtype of closed forms

## Main Results

* `smoothExtDeriv_extDeriv`: d² = 0
* `smoothExtDeriv_wedge`: Leibniz rule for d on wedge products
* `isFormClosed_wedge`: Wedge of closed forms is closed

## Implementation Notes

The exterior derivative `smoothExtDeriv` is implemented via `ContMDiffForm.extDerivForm`,
which uses the manifold derivative `mfderiv`. This is verified by the theorem
`smoothExtDeriv_eq_extDerivForm`.
-/

noncomputable section

open Classical Module Manifold
open scoped Pointwise Manifold TensorProduct

set_option autoImplicit false

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]

/-- The zero form has smooth (constantly zero) coefficients. -/
theorem isSmoothAlternating_zero (k : ℕ) : IsSmoothAlternating n X k (fun _ => 0) :=
  contMDiff_const

instance (k : ℕ) : Zero (SmoothForm n X k) := ⟨⟨fun _ => 0, isSmoothAlternating_zero k⟩⟩

/-- The sum of smooth forms is smooth. -/
theorem isSmoothAlternating_add (k : ℕ) (ω η : SmoothForm n X k) :
    IsSmoothAlternating n X k (fun x => ω.as_alternating x + η.as_alternating x) := by
  let addCLM : (FiberAlt n k × FiberAlt n k) →L[ℝ] FiberAlt n k :=
    ContinuousLinearMap.fst ℝ (FiberAlt n k) (FiberAlt n k) +
    ContinuousLinearMap.snd ℝ (FiberAlt n k) (FiberAlt n k)
  exact addCLM.contMDiff.comp (ω.is_smooth.prodMk_space η.is_smooth)

/-- The negation of a smooth form is smooth. -/
theorem isSmoothAlternating_neg (k : ℕ) (ω : SmoothForm n X k) :
    IsSmoothAlternating n X k (fun x => -ω.as_alternating x) := by
  let negCLM : FiberAlt n k →L[ℝ] FiberAlt n k := -ContinuousLinearMap.id ℝ (FiberAlt n k)
  exact negCLM.contMDiff.comp ω.is_smooth

/-- For a fixed continuous alternating map, the "evaluation-on-the-unit-ball" set is bounded above.
This is the basic boundedness input for `sSup`-based operator norms. -/
theorem IsSmoothAlternating.bddAbove {k : ℕ} (f : FiberAlt n k) :
    BddAbove { r : ℝ | ∃ v : Fin k → TangentModel n, (∀ i, ‖v i‖ ≤ 1) ∧ r = ‖f v‖ } := by
  refine ⟨‖f‖, ?_⟩
  rintro r ⟨v, hv, rfl⟩
  -- Use the operator-norm bound `‖f v‖ ≤ ‖f‖ * ∏ i ‖v i‖` and `∏ i ‖v i‖ ≤ 1`.
  have hprod : (∏ i : Fin k, ‖v i‖) ≤ 1 := by
    classical
    -- each factor is in `[0,1]`
    refine Finset.prod_le_one ?_ ?_
    · intro i _; exact norm_nonneg _
    · intro i _; simpa using hv i
  have hle : ‖f v‖ ≤ ‖f‖ * (∏ i : Fin k, ‖v i‖) := by
    simpa using (ContinuousAlternatingMap.le_opNorm (f := f) v)
  calc
    ‖f v‖ ≤ ‖f‖ * (∏ i : Fin k, ‖v i‖) := hle
    _ ≤ ‖f‖ * 1 := by gcongr
    _ = ‖f‖ := by simp

/-- Scalar multiplication preserves smoothness. -/
theorem isSmoothAlternating_smul (k : ℕ) (c : ℂ) (ω : SmoothForm n X k) :
    IsSmoothAlternating n X k (fun x => c • ω.as_alternating x) := by
  let smulCLM : FiberAlt n k →L[ℝ] FiberAlt n k := c • ContinuousLinearMap.id ℝ (FiberAlt n k)
  exact smulCLM.contMDiff.comp ω.is_smooth


/-- The difference of smooth forms is smooth (follows from add and neg). -/
theorem isSmoothAlternating_sub (k : ℕ) (ω η : SmoothForm n X k) :
    IsSmoothAlternating n X k (fun x => ω.as_alternating x - η.as_alternating x) := by
  let subCLM : (FiberAlt n k × FiberAlt n k) →L[ℝ] FiberAlt n k :=
    ContinuousLinearMap.fst ℝ (FiberAlt n k) (FiberAlt n k) -
    ContinuousLinearMap.snd ℝ (FiberAlt n k) (FiberAlt n k)
  exact subCLM.contMDiff.comp (ω.is_smooth.prodMk_space η.is_smooth)

instance (k : ℕ) : Add (SmoothForm n X k) := ⟨fun ω η => ⟨fun x => ω.as_alternating x + η.as_alternating x, isSmoothAlternating_add k ω η⟩⟩
instance (k : ℕ) : Neg (SmoothForm n X k) := ⟨fun ω => ⟨fun x => -ω.as_alternating x, isSmoothAlternating_neg k ω⟩⟩
instance (k : ℕ) : Sub (SmoothForm n X k) := ⟨fun ω η => ⟨fun x => ω.as_alternating x - η.as_alternating x, isSmoothAlternating_sub k ω η⟩⟩
instance (k : ℕ) : SMul ℂ (SmoothForm n X k) := ⟨fun c ω => ⟨fun x => c • ω.as_alternating x, isSmoothAlternating_smul k c ω⟩⟩
instance (k : ℕ) : SMul ℝ (SmoothForm n X k) :=
  ⟨fun r ω => ⟨fun x => r • ω.as_alternating x, isSmoothAlternating_smul k (r : ℂ) ω⟩⟩

@[simp] lemma SmoothForm.zero_apply (k : ℕ) (x : X) : (0 : SmoothForm n X k).as_alternating x = 0 := rfl
@[simp] lemma SmoothForm.add_apply (k : ℕ) (ω η : SmoothForm n X k) (x : X) : (ω + η).as_alternating x = ω.as_alternating x + η.as_alternating x := rfl
@[simp] lemma SmoothForm.neg_apply (k : ℕ) (ω : SmoothForm n X k) (x : X) : (-ω).as_alternating x = -ω.as_alternating x := rfl
@[simp] lemma SmoothForm.sub_apply (k : ℕ) (ω η : SmoothForm n X k) (x : X) : (ω - η).as_alternating x = ω.as_alternating x - η.as_alternating x := rfl
@[simp] lemma SmoothForm.smul_apply (k : ℕ) (c : ℂ) (ω : SmoothForm n X k) (x : X) : (c • ω).as_alternating x = c • ω.as_alternating x := rfl
@[simp] lemma SmoothForm.smul_real_apply (k : ℕ) (r : ℝ) (ω : SmoothForm n X k) (x : X) :
    (r • ω).as_alternating x = r • ω.as_alternating x := rfl

/-- Cast a `SmoothForm` between equal degrees. -/
def castForm {k k' : ℕ} (h : k = k') (ω : SmoothForm n X k) : SmoothForm n X k' :=
  h ▸ ω

@[simp] lemma castForm_refl (k : ℕ) (ω : SmoothForm n X k) : castForm rfl ω = ω := rfl

@[simp] lemma castForm_zero {k k' : ℕ} (h : k = k') : castForm h (0 : SmoothForm n X k) = 0 := by
  subst h; rfl

@[simp] lemma SmoothForm.castForm_as_alternating {k k' : ℕ} (h : k = k') (ω : SmoothForm n X k) (x : X) :
    (castForm h ω).as_alternating x = h ▸ ω.as_alternating x := by
  subst h; rfl

theorem castForm_tsupport_eq {k k' : ℕ} (h : k = k') (ω : SmoothForm n X k) :
    tsupport (castForm h ω).as_alternating = tsupport ω.as_alternating := by
  subst h; rfl

theorem castForm_hasCompactSupport {k k' : ℕ} (h : k = k') (ω : SmoothForm n X k) :
    HasCompactSupport ω.as_alternating →
      HasCompactSupport (castForm h ω).as_alternating := by
  intro hcomp
  subst h
  simpa using hcomp

instance (k : ℕ) : AddCommGroup (SmoothForm n X k) where
  add := (· + ·)
  zero := 0
  neg := (- ·)
  sub := (· - ·)
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := fun ω η θ => by
    apply SmoothForm.ext; funext x; simp only [SmoothForm.add_apply, add_assoc]
  zero_add := fun ω => by
    apply SmoothForm.ext; funext x; simp only [SmoothForm.add_apply, SmoothForm.zero_apply, zero_add]
  add_zero := fun ω => by
    apply SmoothForm.ext; funext x; simp only [SmoothForm.add_apply, SmoothForm.zero_apply, add_zero]
  neg_add_cancel := fun ω => by
    apply SmoothForm.ext; funext x; simp only [SmoothForm.add_apply, SmoothForm.neg_apply, SmoothForm.zero_apply, neg_add_cancel]
  add_comm := fun ω η => by
    apply SmoothForm.ext; funext x; simp only [SmoothForm.add_apply, add_comm]
  sub_eq_add_neg := fun ω η => by
    apply SmoothForm.ext; funext x; simp only [SmoothForm.sub_apply, SmoothForm.add_apply, SmoothForm.neg_apply, sub_eq_add_neg]

instance (k : ℕ) : Module ℂ (SmoothForm n X k) where
  one_smul ω := by
    ext x v
    simp
  mul_smul c c' ω := by
    ext x v
    simp [mul_assoc]
  smul_zero c := by
    ext x v
    simp
  smul_add c ω η := by
    ext x v
    simp [mul_add]
  add_smul c c' ω := by
    ext x v
    simp [add_mul]
  zero_smul ω := by
    ext x v
    simp

instance (k : ℕ) : Module ℝ (SmoothForm n X k) where
  one_smul ω := by
    ext x v
    simp
  mul_smul r s ω := by
    ext x v
    simp [mul_assoc]
  smul_zero r := by
    ext x v
    simp
  smul_add r ω η := by
    ext x v
    simp [mul_add]
  add_smul r s ω := by
    ext x v
    simp [add_mul]
  zero_smul ω := by
    ext x v
    simp

/-!
### Exterior Derivative on Smooth Forms

The exterior derivative `d : Ωᵏ(X) → Ωᵏ⁺¹(X)` is defined using axioms that capture
its fundamental properties. The construction uses the manifold derivative `mfderiv`
followed by alternatization:

  `(dω)ₓ(v₀, v₁, ..., vₖ) = Alt(D(ω)(x))(v₀, v₁, ..., vₖ)`

where `D(ω)(x) : TₓX → Altᵏ(TₓX, ℂ)` is the derivative of the coefficient map.

**Key properties** (axiomatized below):
- Linearity: `d(αω + βη) = α·dω + β·dη`
- `d² = 0`: `d(dω) = 0` (by symmetry of second derivatives)
- Leibniz: `d(ω ∧ η) = dω ∧ η + (-1)^k ω ∧ dη`
-/

/-!
## SmoothForm ↔ ContMDiffForm Conversion (Algebraic Structure Lemmas)

These lemmas show that the conversion between SmoothForm and ContMDiffForm respects
the algebraic structure. They are placed here (in Forms.lean) rather than in
ContMDiffForms.lean because they depend on the Add/SMul instances for SmoothForm
which are defined in this file.
-/

/-- `toContMDiffForm` respects addition. -/
lemma SmoothForm.toContMDiffForm_add {k : ℕ} (ω η : SmoothForm n X k) :
    (ω + η).toContMDiffForm = ω.toContMDiffForm + η.toContMDiffForm := by
  refine ContMDiffForm.ext _ _ (fun x => ?_)
  rfl

/-- `toContMDiffForm` respects scalar multiplication. -/
lemma SmoothForm.toContMDiffForm_smul {k : ℕ} (c : ℂ) (ω : SmoothForm n X k) :
    (c • ω).toContMDiffForm = c • ω.toContMDiffForm := by
  refine ContMDiffForm.ext _ _ (fun x => ?_)
  rfl

/-- `toSmoothForm` respects addition. -/
lemma ContMDiffForm.toSmoothForm_add {k : ℕ} (ω η : ContMDiffForm n X k) :
    (ω + η).toSmoothForm = ω.toSmoothForm + η.toSmoothForm := by
  apply SmoothForm.ext
  funext x
  rfl

/-- `toSmoothForm` respects scalar multiplication. -/
lemma ContMDiffForm.toSmoothForm_smul {k : ℕ} (c : ℂ) (ω : ContMDiffForm n X k) :
    (c • ω).toSmoothForm = c • ω.toSmoothForm := by
  apply SmoothForm.ext
  funext x
  rfl

/-- **The exterior derivative as a ℂ-linear map** (Classical Pillar Axiom).

## Mathematical Definition

The exterior derivative `d : Ωᵏ(X) → Ωᵏ⁺¹(X)` is the unique linear operator satisfying:

1. **Linearity**: `d(αω + βη) = α·dω + β·dη` for α, β ∈ ℂ
2. **Nilpotency** (`d² = 0`): `d(dω) = 0` for all forms ω
3. **Leibniz rule**: `d(ω ∧ η) = dω ∧ η + (-1)^deg(ω) ω ∧ dη`
4. **Agreement with differential**: On 0-forms (functions), d agrees with the differential

## Axiomatization Justification

This is axiomatized as a **Classical Pillar** because:

1. **Mathlib Gap**: The full construction requires composing `mfderiv` (the Fréchet
   derivative on manifolds) with `alternatization` to produce alternating forms.
   Mathlib's current API for `ContMDiffAt` and `mfderiv` does not directly support
   this composition at the smooth bundle level.

2. **Standard Mathematics**: The existence and properties of d are completely
   standard and appear in every differential geometry textbook. The construction
   is well-understood since Cartan (1899) and formalized in:
   - [Warner, "Foundations of Differentiable Manifolds and Lie Groups", Ch. 2]
   - [Spivak, "Calculus on Manifolds", Ch. 4]
   - [Lee, "Introduction to Smooth Manifolds", Ch. 14]

3. **Sound Axiomatization**: The axiom asserts only the existence of a ℂ-linear map
   with no additional properties beyond linearity. The key properties (`d² = 0`,
   Leibniz rule) are stated as separate axioms that can be individually verified.

## Role in Proof

This axiom is **ON THE PROOF TRACK** for `hodge_conjecture'`. It is used to:
- Define closed forms (kernel of d)
- Define exact forms (image of d)
- Construct de Rham cohomology H^k(X) = ker(d)/im(d)

## References

- [É. Cartan, "Sur certaines expressions différentielles", 1899]
- [Warner, "Foundations of Differentiable Manifolds and Lie Groups", GTM 94, Ch. 2]
- [Bott-Tu, "Differential Forms in Algebraic Topology", GTM 82, Ch. I]
- [Lee, "Introduction to Smooth Manifolds", 2nd ed., Springer, 2012, Ch. 14]
-/
noncomputable def extDerivLinearMap (n : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X]
    [HasLocallyConstantCharts n X] (k : ℕ) :
    SmoothForm n X k →ₗ[ℂ] SmoothForm n X (k + 1) where
  toFun ω := (ContMDiffForm.extDerivForm ω.toContMDiffForm HasLocallyConstantCharts.hCharts).toSmoothForm
  map_add' := fun ω η => by
    rw [SmoothForm.toContMDiffForm_add]
    rw [ContMDiffForm.extDerivForm_add]
    rw [ContMDiffForm.toSmoothForm_add]
  map_smul' := fun c ω => by
    simp only [RingHom.id_apply]
    rw [SmoothForm.toContMDiffForm_smul]
    rw [ContMDiffForm.extDerivForm_smul]
    rw [ContMDiffForm.toSmoothForm_smul]

/-- The exterior derivative of a smooth form. -/
noncomputable def smoothExtDeriv {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X (k + 1) :=
  extDerivLinearMap n X k ω

/-- **Connection theorem**: `smoothExtDeriv` is implemented via `ContMDiffForm.extDerivForm`.

This theorem explicitly shows that `smoothExtDeriv` is the genuine exterior derivative
computed using manifold derivatives (`mfderiv`), not a trivial stub.

The implementation chain is:
1. `smoothExtDeriv ω` = `extDerivLinearMap n X k ω`
2. `extDerivLinearMap` is defined as `(ContMDiffForm.extDerivForm ω.toContMDiffForm hCharts).toSmoothForm`
3. `ContMDiffForm.extDerivForm` uses `ContMDiffForm.extDeriv` which is based on `mfderiv`
-/
theorem smoothExtDeriv_eq_extDerivForm {k : ℕ} (ω : SmoothForm n X k) :
    smoothExtDeriv ω =
      (ContMDiffForm.extDerivForm ω.toContMDiffForm HasLocallyConstantCharts.hCharts).toSmoothForm := by
  rfl

/-- `smoothExtDeriv` is non-trivial: it uses the real manifold exterior derivative. -/
theorem smoothExtDeriv_nontrivial {k : ℕ} :
    (smoothExtDeriv : SmoothForm n X k → SmoothForm n X (k + 1)) =
      fun ω => (ContMDiffForm.extDerivForm ω.toContMDiffForm HasLocallyConstantCharts.hCharts).toSmoothForm := by
  rfl

@[simp] theorem smoothExtDeriv_zero {k : ℕ} : smoothExtDeriv (0 : SmoothForm n X k) = 0 := by
  simp only [smoothExtDeriv, map_zero]

theorem smoothExtDeriv_eq_zero_of_eq_zero_on {k : ℕ} (ω : SmoothForm n X k) {U : Set X}
    (hU : IsOpen U) (hzero : ∀ x ∈ U, ω.as_alternating x = 0) :
    ∀ x ∈ U, (smoothExtDeriv ω).as_alternating x = 0 := by
  intro x hx
  have hzero' : ω.as_alternating =ᶠ[nhds x] 0 := by
    refine Filter.eventuallyEq_of_mem (hU.mem_nhds hx) ?_
    intro y hy
    exact hzero y hy
  have hmf :
      mfderiv (𝓒_complex n) 𝓘(ℝ, FiberAlt n k) ω.as_alternating x = 0 := by
    have hmf_eq :
        mfderiv (𝓒_complex n) 𝓘(ℝ, FiberAlt n k) ω.as_alternating x =
          mfderiv (𝓒_complex n) 𝓘(ℝ, FiberAlt n k) (fun _ : X => (0 : FiberAlt n k)) x :=
      Filter.EventuallyEq.mfderiv_eq (I := 𝓒_complex n) (I' := 𝓘(ℝ, FiberAlt n k)) hzero'
    simpa using hmf_eq
  -- Expand `smoothExtDeriv` to the pointwise alternating map.
  unfold smoothExtDeriv extDerivLinearMap
  simp only [LinearMap.coe_mk, AddHom.coe_mk, ContMDiffForm.toSmoothForm_as_alternating,
    ContMDiffForm.extDerivForm_as_alternating, ContMDiffForm.extDeriv_as_alternating,
    ContMDiffForm.extDerivAt_def, SmoothForm.toContMDiffForm_as_alternating, hmf]
  simp only [ContinuousAlternatingMap.alternatizeUncurryFin]
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (TangentModel n) ℂ (n := k)).map_zero

private lemma smoothExtDeriv_eventuallyEq_zero_of_eventuallyEq_zero {k : ℕ} (ω : SmoothForm n X k)
    {x : X} (hzero : ω.as_alternating =ᶠ[nhds x] 0) :
    (smoothExtDeriv ω).as_alternating =ᶠ[nhds x] 0 := by
  rcases (Filter.eventuallyEq_iff_exists_mem).1 hzero with ⟨s, hs, hEq⟩
  rcases mem_nhds_iff.mp hs with ⟨U, hUsub, hUopen, hxU⟩
  have hEqU : Set.EqOn ω.as_alternating (fun _ : X => (0 : FiberAlt n k)) U := by
    intro y hy
    exact hEq (hUsub hy)
  have hzeroU :
      ∀ y ∈ U, (smoothExtDeriv ω).as_alternating y = 0 :=
    smoothExtDeriv_eq_zero_of_eq_zero_on (ω := ω) hUopen hEqU
  exact Filter.eventuallyEq_of_mem (hUopen.mem_nhds hxU) hzeroU

theorem smoothExtDeriv_tsupport_subset {k : ℕ} (ω : SmoothForm n X k) :
    tsupport (smoothExtDeriv ω).as_alternating ⊆ tsupport ω.as_alternating := by
  intro x hx
  by_contra hx'
  have hzero : ω.as_alternating =ᶠ[nhds x] 0 :=
    (notMem_tsupport_iff_eventuallyEq).1 hx'
  have hzero' :
      (smoothExtDeriv ω).as_alternating =ᶠ[nhds x] 0 :=
    smoothExtDeriv_eventuallyEq_zero_of_eventuallyEq_zero (ω := ω) hzero
  have hxnot : x ∉ tsupport (smoothExtDeriv ω).as_alternating :=
    (notMem_tsupport_iff_eventuallyEq).2 hzero'
  exact hxnot hx

theorem smoothExtDeriv_hasCompactSupport {k : ℕ} (ω : SmoothForm n X k) :
    HasCompactSupport ω.as_alternating →
      HasCompactSupport (smoothExtDeriv ω).as_alternating := by
  intro hcomp
  have hcompact : IsCompact (tsupport ω.as_alternating) := by
    simpa [HasCompactSupport] using hcomp
  have hcompact' :
      IsCompact (tsupport (smoothExtDeriv ω).as_alternating) :=
    IsCompact.of_isClosed_subset hcompact (isClosed_tsupport _)
      (smoothExtDeriv_tsupport_subset (ω := ω))
  simpa [HasCompactSupport] using hcompact'

def IsFormClosed {k : ℕ} (ω : SmoothForm n X k) : Prop := smoothExtDeriv ω = 0

theorem isFormClosed_zero {k : ℕ} : IsFormClosed (0 : SmoothForm n X k) := by
  unfold IsFormClosed
  exact smoothExtDeriv_zero

theorem isFormClosed_add {k : ℕ} {ω η : SmoothForm n X k} :
    IsFormClosed ω → IsFormClosed η → IsFormClosed (ω + η) := by
  intro hω hη
  unfold IsFormClosed at hω hη ⊢
  have hω' : (extDerivLinearMap n X k) ω = 0 := by
    simpa [smoothExtDeriv] using hω
  have hη' : (extDerivLinearMap n X k) η = 0 := by
    simpa [smoothExtDeriv] using hη
  change (extDerivLinearMap n X k) (ω + η) = 0
  rw [map_add (extDerivLinearMap n X k) ω η, hω', hη']
  simp

@[simp] theorem smoothExtDeriv_neg {k : ℕ} (ω : SmoothForm n X k) :
    smoothExtDeriv (-ω) = -smoothExtDeriv ω := map_neg (extDerivLinearMap n X k) ω

@[simp] theorem smoothExtDeriv_sub {k : ℕ} (ω η : SmoothForm n X k) :
    smoothExtDeriv (ω - η) = smoothExtDeriv ω - smoothExtDeriv η :=
  map_sub (extDerivLinearMap n X k) ω η

theorem isFormClosed_neg {k : ℕ} {ω : SmoothForm n X k} : IsFormClosed ω → IsFormClosed (-ω) := by
  intro hω; unfold IsFormClosed at *; rw [smoothExtDeriv_neg, hω]; simp

theorem isFormClosed_sub {k : ℕ} {ω η : SmoothForm n X k} :
    IsFormClosed ω → IsFormClosed η → IsFormClosed (ω - η) := by
  intros hω hη; unfold IsFormClosed at *; rw [smoothExtDeriv_sub, hω, hη]; simp

theorem isFormClosed_smul {k : ℕ} {c : ℂ} {ω : SmoothForm n X k} :
    IsFormClosed ω → IsFormClosed (c • ω) := by
  intro hω
  unfold IsFormClosed at hω ⊢
  have hω' : (extDerivLinearMap n X k) ω = 0 := by
    simpa [smoothExtDeriv] using hω
  change (extDerivLinearMap n X k) (c • ω) = 0
  rw [map_smul (extDerivLinearMap n X k) c ω, hω']
  simp

theorem isFormClosed_smul_real {k : ℕ} {r : ℝ} {ω : SmoothForm n X k} :
    IsFormClosed ω → IsFormClosed (r • ω) := by
  intro hω
  have h : (r • ω) = ((r : ℂ) • ω) := rfl
  rw [h]
  exact isFormClosed_smul hω

def IsExact {k : ℕ} (ω : SmoothForm n X k) : Prop :=
  match k with
  | 0 => ω = 0
  | k' + 1 => ∃ (η : SmoothForm n X k'), smoothExtDeriv η = ω

/-- The zero form is exact at any degree. -/
theorem isExact_zero {k : ℕ} : IsExact (0 : SmoothForm n X k) := by
  unfold IsExact
  cases k with
  | zero => rfl
  | succ k' => exact ⟨0, smoothExtDeriv_zero⟩

structure ClosedForm (n : ℕ) (X : Type u) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] where
  val : SmoothForm n X k
  property : IsFormClosed val

namespace ClosedForm
variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X]
  [HasLocallyConstantCharts n X]
instance (k : ℕ) : Add (ClosedForm n X k) := ⟨fun ω η => ⟨ω.val + η.val, isFormClosed_add ω.property η.property⟩⟩
instance (k : ℕ) : Neg (ClosedForm n X k) := ⟨fun ω => ⟨-ω.val, isFormClosed_neg ω.property⟩⟩
instance (k : ℕ) : Zero (ClosedForm n X k) := ⟨⟨0, isFormClosed_zero⟩⟩
end ClosedForm

/-- **Wedge Product Preserves Smoothness** (Classical Pillar Axiom).

## Mathematical Statement

The wedge product of two smooth differential forms is smooth:
If ω ∈ Ω^k(X) and η ∈ Ω^l(X) are smooth, then ω ∧ η ∈ Ω^{k+l}(X) is smooth.

## Mathematical Definition

For forms ω ∈ Ω^k(X) and η ∈ Ω^l(X), the wedge product is defined pointwise:

  `(ω ∧ η)_x(v₁,...,v_{k+l}) = (1/k!l!) Σ_σ sign(σ) ω_x(v_σ(1),...,v_σ(k)) · η_x(v_σ(k+1),...,v_σ(k+l))`

where the sum is over all permutations σ of {1,...,k+l}.

## Axiomatization Justification

This is axiomatized as a **Classical Pillar** because:

1. **Mathlib Gap**: The proof requires showing that the composition
   `x ↦ wedge(ω(x), η(x))` is `ContMDiff`. This requires:
   - `wedge` to be registered as a smooth bilinear map
   - Composition with smooth bundle sections
   Mathlib's bundle API doesn't directly support this.

2. **Standard Mathematics**: Smoothness of wedge is immediate from:
   - Wedge is a bilinear operation on finite-dimensional vector spaces
   - Composition of smooth maps is smooth
   This appears in every differential geometry text.

## Role in Proof

This axiom is **ON THE PROOF TRACK** for `hodge_conjecture'`. It is used to:
- Define `smoothWedge : SmoothForm n X k → SmoothForm n X l → SmoothForm n X (k+l)`
- Construct the cup product on cohomology

## References

- [Warner, "Foundations of Differentiable Manifolds and Lie Groups", GTM 94, Ch. 2]
- [Lee, "Introduction to Smooth Manifolds", 2nd ed., Ch. 14]
- [Spivak, "Calculus on Manifolds", Ch. 4]
-/
theorem isSmoothAlternating_wedge (k l : ℕ) (ω : SmoothForm n X k) (η : SmoothForm n X l) :
    IsSmoothAlternating n X (k + l)
      (fun x => ContinuousAlternatingMap.wedgeℂ (E := TangentModel n)
                  (ω.as_alternating x) (η.as_alternating x)) := by
  -- `wedgeℂCLM_alt` is a continuous bilinear map; composition with smooth maps is smooth.
  let f := (ContinuousAlternatingMap.wedgeℂCLM_alt (E := TangentModel n) k l)
  exact f.contMDiff.comp ω.is_smooth |>.clm_apply η.is_smooth

noncomputable def smoothWedge {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l) : SmoothForm n X (k + l) where
  as_alternating := fun x =>
    ContinuousAlternatingMap.wedgeℂ (E := TangentModel n)
      (ω.as_alternating x) (η.as_alternating x)
  is_smooth := isSmoothAlternating_wedge k l ω η

notation:67 ω:68 " ⋏ " η:68 => smoothWedge ω η

@[simp] lemma SmoothForm.wedge_apply {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l) (x : X) :
    (ω ⋏ η).as_alternating x =
      ContinuousAlternatingMap.wedgeℂ (E := TangentModel n) (ω.as_alternating x) (η.as_alternating x) := rfl

@[simp] lemma zero_wedge {k l : ℕ} (η : SmoothForm n X l) : (0 : SmoothForm n X k) ⋏ η = 0 := by
  ext x v
  simp [smoothWedge, ContinuousAlternatingMap.wedgeℂ_apply, ContinuousAlternatingMap.wedgeℂ_linear]

@[simp] lemma wedge_zero {k l : ℕ} (ω : SmoothForm n X k) : ω ⋏ (0 : SmoothForm n X l) = 0 := by
  ext x v
  simp [smoothWedge, ContinuousAlternatingMap.wedgeℂ_apply, ContinuousAlternatingMap.wedgeℂ_linear]

/-- **Nilpotency of Exterior Derivative: d² = 0** (Classical Pillar Axiom).

## Mathematical Statement

For any smooth differential form ω, applying the exterior derivative twice gives zero:

  `d(dω) = 0`

This is the defining property of a **cochain complex** and makes de Rham cohomology well-defined.

## Mathematical Proof (Classical)

The proof follows from **Schwarz's theorem** (symmetry of mixed partial derivatives):

1. Locally, `dω = Σᵢ (∂ωᵢ/∂xᵢ) dxᵢ ∧ ...`
2. Applying d again: `d(dω) = Σᵢⱼ (∂²ωᵢ/∂xⱼ∂xᵢ) dxⱼ ∧ dxᵢ ∧ ...`
3. By Schwarz: `∂²f/∂xⱼ∂xᵢ = ∂²f/∂xᵢ∂xⱼ` (symmetric)
4. But `dxⱼ ∧ dxᵢ = -dxᵢ ∧ dxⱼ` (antisymmetric)
5. Symmetric coefficients with antisymmetric basis ⟹ sum is zero

## Axiomatization Justification

This is axiomatized as a **Classical Pillar** because:

1. **Mathlib Gap**: The proof requires:
   - Computing `d` explicitly using local coordinates or `mfderiv`
   - Schwarz's theorem for manifold-valued functions
   - Alternatization of the second derivative tensor
   The current `ContMDiff` API doesn't provide these tools directly.

2. **Standard Mathematics**: This is Poincaré's lemma (1895) and appears in:
   - Every differential geometry textbook
   - Every algebraic topology textbook (as a cochain complex property)

## Role in Proof

This axiom is **ON THE PROOF TRACK** for `hodge_conjecture'`. It ensures:
- Exact forms (im d) are closed (ker d)
- De Rham cohomology H^k = ker d / im d is well-defined
- The cohomology class [ω] is independent of representative

## References

- [Poincaré, "Les méthodes nouvelles de la mécanique céleste", 1892-1899]
- [de Rham, "Variétés Différentiables", 1955, Ch. 1]
- [Warner, "Foundations of Differentiable Manifolds", GTM 94, Theorem 2.14]
- [Bott-Tu, "Differential Forms in Algebraic Topology", GTM 82, Ch. 1]

**NOW PROVED** using ContMDiffForm.extDeriv_extDeriv. -/
theorem smoothExtDeriv_extDeriv {k : ℕ} (ω : SmoothForm n X k) :
    smoothExtDeriv (smoothExtDeriv ω) = 0 := by
  -- d²ω = 0 by the symmetry of second derivatives (Schwarz's theorem)
  -- We use the ContMDiffForm.extDeriv_extDeriv infrastructure
  -- smoothExtDeriv ω = (extDerivForm ω.toContMDiffForm hCharts).toSmoothForm
  -- So (smoothExtDeriv ω).toContMDiffForm = (extDerivForm ω.toContMDiffForm hCharts).toSmoothForm.toContMDiffForm
  --                                       = extDerivForm ω.toContMDiffForm hCharts
  --
  -- Then smoothExtDeriv (smoothExtDeriv ω) = (extDerivForm (smoothExtDeriv ω).toContMDiffForm hCharts).toSmoothForm
  --                                        = (extDerivForm (extDerivForm ω.toContMDiffForm hCharts) hCharts).toSmoothForm
  --
  -- By ContMDiffForm.extDeriv_extDeriv: extDeriv (extDerivForm ω.toContMDiffForm hCharts) = 0
  -- The extDerivForm of something with extDeriv = 0 has as_alternating = 0.
  apply SmoothForm.ext
  funext x
  simp only [SmoothForm.zero_apply]
  -- Goal: show (smoothExtDeriv (smoothExtDeriv ω)).as_alternating x = 0
  unfold smoothExtDeriv extDerivLinearMap
  simp only [LinearMap.coe_mk, AddHom.coe_mk, ContMDiffForm.toSmoothForm_as_alternating]
  -- Goal: (extDerivForm ((extDerivForm ω.toContMDiffForm hCharts).toSmoothForm.toContMDiffForm) hCharts).as_alternating x = 0
  simp only [ContMDiffForm.toSmoothForm_toContMDiffForm]
  -- Goal: (extDerivForm (extDerivForm ω.toContMDiffForm hCharts) hCharts).as_alternating x = 0
  simp only [ContMDiffForm.extDerivForm_as_alternating]
  -- Goal: ContMDiffForm.extDeriv (extDerivForm ω.toContMDiffForm hCharts) x = 0
  rw [ContMDiffForm.extDeriv_extDeriv ω.toContMDiffForm HasLocallyConstantCharts.hCharts]
  rfl

/-- **Graded Leibniz Rule for Exterior Derivative** (Classical Pillar Axiom).

## Mathematical Statement

For differential forms ω ∈ Ω^k(X) and η ∈ Ω^l(X):

  `d(ω ∧ η) = dω ∧ η + (-1)^k ω ∧ dη`

This is the **graded Leibniz rule** (or graded product rule) for differential forms.

## Mathematical Content

### The Sign Factor (-1)^k

The sign arises from the graded structure of the exterior algebra:
- Forms of degree k are "odd" if k is odd, "even" if k is even
- Moving d past a k-form requires k "transpositions"
- Each transposition introduces a factor of -1

### Graded Commutativity

This is part of the general principle that Ω^*(X) is a **graded-commutative algebra**:
- `ω ∧ η = (-1)^{kl} η ∧ ω`
- `d` is a **graded derivation** of degree +1

## Axiomatization Justification

This is axiomatized as a **Classical Pillar** because:

1. **Mathlib Gap**: The proof requires:
   - Local coordinate computation of d(ω ∧ η)
   - Tracking signs through alternatization
   - The product rule for each coordinate function
   This is tedious but completely standard.

2. **Standard Mathematics**: The Leibniz rule is fundamental to:
   - Cartan's calculus of differential forms
   - De Rham cohomology (cup product is well-defined)
   - Every computation in differential geometry

## Role in Proof

This axiom is **ON THE PROOF TRACK** for `hodge_conjecture'`. It is used to:
- Prove that wedge of closed forms is closed (`isFormClosed_wedge`)
- Show that cup product is well-defined on cohomology
- Compute the exterior derivative of products

## References

- [É. Cartan, "Les systèmes différentiels extérieurs", 1945]
- [Warner, "Foundations of Differentiable Manifolds", GTM 94, Prop. 2.13]
- [Lee, "Introduction to Smooth Manifolds", 2nd ed., Prop. 14.28]
- [Bott-Tu, "Differential Forms in Algebraic Topology", GTM 82, Ch. 1]
-/
-- Helper lemma: relates domDomCongr-based casts to transport-based casts for wedge products
private lemma castAlt_eq_transport_wedge {m m' : ℕ} (h : m = m')
    (f : FiberAlt n m) :
    f.domDomCongr (finCongr h) = h ▸ f := by
  subst h; rfl

-- Lemma: castForm of smul
private lemma castForm_smul_as_alternating {m m' : ℕ} (h : m = m') (c : ℂ)
    (ω : SmoothForm n X m) (x : X) :
    (castForm h (c • ω)).as_alternating x = h ▸ (c • ω.as_alternating x) := by
  subst h; rfl

-- Lemma: castForm of wedge
private lemma castForm_wedge_as_alternating {k' l' m : ℕ} (h : k' + l' = m)
    (ω : SmoothForm n X k') (η : SmoothForm n X l') (x : X) :
    (castForm h (ω ⋏ η)).as_alternating x =
      h ▸ ContinuousAlternatingMap.wedgeℂ (E := TangentModel n) (ω.as_alternating x) (η.as_alternating x) := by
  subst h; rfl

theorem smoothExtDeriv_wedge {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l) :
    smoothExtDeriv (ω ⋏ η) =
      castForm (by omega : (k + 1) + l = (k + l) + 1) (smoothExtDeriv ω ⋏ η) +
      castForm (by omega : k + (l + 1) = (k + l) + 1) ((-1 : ℂ)^k • (ω ⋏ smoothExtDeriv η)) := by
  -- This proof uses LeibnizRule.extDerivAt_wedge, which depends on
  -- alternatizeUncurryFin_wedge_right and alternatizeUncurryFin_wedge_left
  -- (now proved in `Hodge/Analytic/Advanced/LeibnizRule.lean`)
  apply SmoothForm.ext
  funext x
  -- Compute LHS using LeibnizRule.extDerivAt_wedge
  have h_wedge_eq : (ω ⋏ η).toContMDiffForm = ω.toContMDiffForm.wedge η.toContMDiffForm := by
    apply ContMDiffForm.ext; intro y; rfl
  have h_lhs : (smoothExtDeriv (ω ⋏ η)).as_alternating x =
      ContMDiffForm.extDerivAt (ω.toContMDiffForm.wedge η.toContMDiffForm) x := by
    simp only [smoothExtDeriv, extDerivLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
               ContMDiffForm.toSmoothForm_as_alternating, h_wedge_eq,
               ContMDiffForm.extDerivForm_as_alternating, ContMDiffForm.extDeriv_as_alternating]
  rw [h_lhs, LeibnizRule.extDerivAt_wedge]
  -- Compute RHS
  simp only [SmoothForm.add_apply]
  -- First term: castForm (smoothExtDeriv ω ⋏ η)
  have h_rhs1 : (castForm (by omega : (k + 1) + l = (k + l) + 1) (smoothExtDeriv ω ⋏ η)).as_alternating x =
      (by omega : (k + 1) + l = (k + l) + 1) ▸
        ContinuousAlternatingMap.wedgeℂ (E := TangentModel n) ((smoothExtDeriv ω).as_alternating x) (η.as_alternating x) := by
    exact castForm_wedge_as_alternating _ _ _ _
  -- Second term: castForm ((-1)^k • (ω ⋏ smoothExtDeriv η))
  have h_rhs2 : (castForm (by omega : k + (l + 1) = (k + l) + 1)
      ((-1 : ℂ)^k • (ω ⋏ smoothExtDeriv η))).as_alternating x =
      (by omega : k + (l + 1) = (k + l) + 1) ▸
        ((-1 : ℂ)^k •
          ContinuousAlternatingMap.wedgeℂ (E := TangentModel n) (ω.as_alternating x) ((smoothExtDeriv η).as_alternating x)) := by
    simp only [castForm_smul_as_alternating, SmoothForm.smul_apply, SmoothForm.wedge_apply]
  rw [h_rhs1, h_rhs2]
  -- Now LHS and RHS have the same structure
  simp only [LeibnizRule.castAlt]
  -- Simplify smoothExtDeriv
  simp only [smoothExtDeriv, extDerivLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
             ContMDiffForm.toSmoothForm_as_alternating, SmoothForm.toContMDiffForm_as_alternating,
             ContMDiffForm.extDerivForm_as_alternating, ContMDiffForm.extDeriv_as_alternating]
  -- Convert domDomCongr to ▸
  rw [castAlt_eq_transport_wedge (by omega : (k+1) + l = (k+l) + 1)]
  rw [castAlt_eq_transport_wedge (by omega : k + (l+1) = (k+l) + 1)]

theorem isFormClosed_wedge {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l) :
    IsFormClosed ω → IsFormClosed η → IsFormClosed (ω ⋏ η) := by
  intros hω hη
  unfold IsFormClosed at *
  rw [smoothExtDeriv_wedge]
  rw [hω, hη]
  simp [zero_wedge, wedge_zero]

-- smoothExtDeriv linearity follows from extDerivLinearMap being a linear map
theorem smoothExtDeriv_add {k : ℕ} (ω₁ ω₂ : SmoothForm n X k) :
    smoothExtDeriv (ω₁ + ω₂) = smoothExtDeriv ω₁ + smoothExtDeriv ω₂ :=
  map_add (extDerivLinearMap n X k) ω₁ ω₂

theorem smoothExtDeriv_smul {k : ℕ} (c : ℂ) (ω : SmoothForm n X k) :
    smoothExtDeriv (c • ω) = c • smoothExtDeriv ω :=
  map_smul (extDerivLinearMap n X k) c ω

theorem smoothExtDeriv_smul_real {k : ℕ} (r : ℝ) (ω : SmoothForm n X k) :
    smoothExtDeriv (r • ω) = r • smoothExtDeriv ω :=
  map_smul (extDerivLinearMap n X k) (r : ℂ) ω

-- NOTE: Continuity of `smoothExtDeriv` lives in the Stage-1 functional-analytic layer
-- (it is not true for the pure comass/C⁰ seminorm alone). We intentionally do not
-- assert continuity here in `Forms.lean`.

/-- The unit 0-form (constant `1`).

This is the intended multiplicative unit for the wedge/cup product on cohomology.
At the level of `FiberAlt n 0`, a 0-form is just a scalar. -/
def unitForm : SmoothForm n X 0 where
  as_alternating := fun _ =>
    haveI : IsEmpty (Fin 0) := Fin.isEmpty
    ContinuousAlternatingMap.constOfIsEmpty ℝ (TangentModel n) (ι := Fin 0) (1 : ℂ)
  is_smooth := contMDiff_const

/-- **The Unit Form is Closed: d(1) = 0** (Classical Pillar Axiom).

## Mathematical Statement

The constant function 1 (viewed as a 0-form) has zero exterior derivative:

  `d(1) = 0`

## Mathematical Proof (Classical)

For a constant function f = c on a manifold X:
- The exterior derivative of a function is `df = Σᵢ (∂f/∂xᵢ) dxᵢ`
- Since f is constant, all partial derivatives vanish: `∂f/∂xᵢ = 0`
- Therefore `df = 0`

In particular, for the constant function 1, we have `d(1) = 0`.

## Axiomatization Justification

This is axiomatized as a **Classical Pillar** because:

1. **Mathlib Gap**: The proof requires:
   - Showing that `extDerivLinearMap` applied to a constant form is zero
   - This would need the explicit construction of d via `mfderiv`
   - The fact that `mfderiv` of a constant function is zero

2. **Standard Mathematics**: This is completely trivial:
   - Constants have zero derivative in any calculus
   - Appears as the first example in any differential forms text

## Role in Proof

This axiom is **ON THE PROOF TRACK** for `hodge_conjecture'`. It ensures:
- The unit class [1] is well-defined in H^0(X)
- [1] is the multiplicative identity for the cup product
- The cohomology ring has a unit element

## References

- [Warner, "Foundations of Differentiable Manifolds", GTM 94, Ch. 2]
- [Lee, "Introduction to Smooth Manifolds", 2nd ed., Example 14.10]
- [Bott-Tu, "Differential Forms in Algebraic Topology", GTM 82, Ch. 1]

**NOW PROVED** using mfderiv_const (the derivative of a constant is 0). -/
theorem isFormClosed_unitForm : IsFormClosed (unitForm (n := n) (X := X)) := by
  -- d(constant) = 0 because mfderiv of a constant is 0
  -- The proof uses: mfderiv_const and alternatizeUncurryFin 0 = 0
  unfold IsFormClosed smoothExtDeriv extDerivLinearMap
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  -- Goal: (extDerivForm unitForm.toContMDiffForm hCharts).toSmoothForm = 0
  apply SmoothForm.ext
  funext x
  simp only [SmoothForm.zero_apply, ContMDiffForm.toSmoothForm_as_alternating,
             ContMDiffForm.extDerivForm_as_alternating]
  -- Goal: ContMDiffForm.extDeriv unitForm.toContMDiffForm x = 0
  simp only [ContMDiffForm.extDeriv_as_alternating, ContMDiffForm.extDerivAt_def]
  -- Goal: alternatizeUncurryFin (mfderiv unitForm.as_alternating x) = 0
  -- unitForm.as_alternating = const (constOfIsEmpty 1), so mfderiv = 0
  -- mfderiv of a constant function is 0
  have h_mf_zero : mfderiv (𝓒_complex n) 𝓘(ℝ, FiberAlt n 0)
      (unitForm (n := n) (X := X)).as_alternating x = 0 := by
    unfold unitForm
    exact mfderiv_const
  rw [SmoothForm.toContMDiffForm_as_alternating, h_mf_zero]
  -- alternatizeUncurryFin 0 = 0 because it's a linear map
  simp only [ContinuousAlternatingMap.alternatizeUncurryFin]
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (TangentModel n) ℂ (n := 0)).map_zero

theorem smoothWedge_add_left {k l : ℕ} (ω₁ ω₂ : SmoothForm n X k) (η : SmoothForm n X l) :
    (ω₁ + ω₂) ⋏ η = (ω₁ ⋏ η) + (ω₂ ⋏ η) := by
  ext x v
  simp [smoothWedge, ContinuousAlternatingMap.wedgeℂ_add_left]

theorem smoothWedge_add_right {k l : ℕ} (ω : SmoothForm n X k) (η₁ η₂ : SmoothForm n X l) :
    ω ⋏ (η₁ + η₂) = (ω ⋏ η₁) + (ω ⋏ η₂) := by
  ext x v
  simp [smoothWedge, ContinuousAlternatingMap.wedgeℂ_add_right]

/-!
### Complex scalar linearity for `wedgeℂ_linear`

`wedgeℂ` is defined over the real base field `ℝ`, but our forms are `ℂ`-valued and we equip
`SmoothForm` with a `Module ℂ` structure. For the wedge algebra on forms, we need the pointwise
identity

`(c • ω) ⋏ η = c • (ω ⋏ η)` and `ω ⋏ (c • η) = c • (ω ⋏ η)`.

The core algebraic statements reduce to `wedgeℂ_linear`, and are proved by unfolding to
`AlternatingMap.domCoprod.summand` and `LinearMap.mul'`.
-/

private lemma domCoprod_summand_smul_left_complex {k l : ℕ} (c : ℂ)
    (ω : (TangentModel n) [⋀^Fin k]→ₗ[ℝ] ℂ) (η : (TangentModel n) [⋀^Fin l]→ₗ[ℝ] ℂ)
    (σ : Equiv.Perm.ModSumCongr (Fin k) (Fin l))
    (v : Fin (k + l) → TangentModel n) :
    (AlternatingMap.domCoprod.summand (c • ω) η σ) (v ∘ finSumFinEquiv) =
      c • (AlternatingMap.domCoprod.summand ω η σ) (v ∘ finSumFinEquiv) := by
  classical
  refine Quotient.inductionOn' σ ?_
  intro σ
  -- After unfolding, this is just bookkeeping: `TensorProduct`'s `ℂ`-smul scales the left factor.
  simp [AlternatingMap.domCoprod.summand, TensorProduct.smul_tmul']
  -- Commute the (±1)-action from `sign σ` with complex multiplication.
  simp [Units.smul_def, zsmul_eq_mul, mul_left_comm, mul_comm]

private lemma mul'_smul_complex (c : ℂ) (t : ℂ ⊗[ℝ] ℂ) :
    (LinearMap.mul' ℝ ℂ) (c • t) = c * (LinearMap.mul' ℝ ℂ t) := by
  refine t.induction_on ?hz ?ht ?ha
  · simp
  · intro a b
    simp [TensorProduct.smul_tmul', mul_assoc]
  · intro x y hx hy
    simp [map_add, hx, hy, mul_add]

private lemma wedgeℂ_linear_smul_left_complex {k l : ℕ} (c : ℂ)
    (ω : FiberAlt n k) (η : FiberAlt n l) (v : Fin (k + l) → TangentModel n) :
    (ContinuousAlternatingMap.wedgeℂ_linear (E := TangentModel n) (c • ω) η) v =
      c * (ContinuousAlternatingMap.wedgeℂ_linear (E := TangentModel n) ω η) v := by
  classical
  simp [ContinuousAlternatingMap.wedgeℂ_linear, domCoprod_summand_smul_left_complex, mul'_smul_complex,
    Finset.mul_sum]

private lemma sign_smul_mul_left {k l : ℕ} (σ : Equiv.Perm (Fin k ⊕ Fin l)) (c a : ℂ) :
    (Equiv.Perm.sign σ • (c * a)) = c * (Equiv.Perm.sign σ • a) := by
  simp [Units.smul_def, zsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm]

private lemma mul'_domCoprod_summand_smul_right_complex {k l : ℕ} (c : ℂ)
    (ω : (TangentModel n) [⋀^Fin k]→ₗ[ℝ] ℂ) (η : (TangentModel n) [⋀^Fin l]→ₗ[ℝ] ℂ)
    (σ : Equiv.Perm.ModSumCongr (Fin k) (Fin l))
    (v : Fin (k + l) → TangentModel n) :
    (LinearMap.mul' ℝ ℂ)
        ((AlternatingMap.domCoprod.summand ω (c • η) σ) (v ∘ finSumFinEquiv)) =
      c * (LinearMap.mul' ℝ ℂ)
        ((AlternatingMap.domCoprod.summand ω η σ) (v ∘ finSumFinEquiv)) := by
  classical
  refine Quotient.inductionOn' σ ?_
  intro σ
  simp [AlternatingMap.domCoprod.summand, sign_smul_mul_left, mul_assoc, mul_left_comm, mul_comm]

private lemma wedgeℂ_linear_smul_right_complex {k l : ℕ} (c : ℂ)
    (ω : FiberAlt n k) (η : FiberAlt n l) (v : Fin (k + l) → TangentModel n) :
    (ContinuousAlternatingMap.wedgeℂ_linear (E := TangentModel n) ω (c • η)) v =
      c * (ContinuousAlternatingMap.wedgeℂ_linear (E := TangentModel n) ω η) v := by
  classical
  simp [ContinuousAlternatingMap.wedgeℂ_linear, mul'_domCoprod_summand_smul_right_complex, Finset.mul_sum]

theorem smoothWedge_smul_left {k l : ℕ} (c : ℂ) (ω : SmoothForm n X k) (η : SmoothForm n X l) :
    (c • ω) ⋏ η = c • (ω ⋏ η) := by
  ext x v
  -- reduce to `wedgeℂ_linear` and apply the complex scalar linearity lemma
  simp [smoothWedge, ContinuousAlternatingMap.wedgeℂ_apply, ContinuousAlternatingMap.smul_apply,
    wedgeℂ_linear_smul_left_complex, smul_eq_mul]

theorem smoothWedge_smul_right {k l : ℕ} (c : ℂ) (ω : SmoothForm n X k) (η : SmoothForm n X l) :
    ω ⋏ (c • η) = c • (ω ⋏ η) := by
  ext x v
  simp [smoothWedge, ContinuousAlternatingMap.wedgeℂ_apply, ContinuousAlternatingMap.smul_apply,
    wedgeℂ_linear_smul_right_complex, smul_eq_mul]

theorem smoothWedge_zero_left {k l : ℕ} (η : SmoothForm n X l) :
    (0 : SmoothForm n X k) ⋏ η = 0 := zero_wedge η

theorem smoothWedge_zero_right {k l : ℕ} (ω : SmoothForm n X k) :
    ω ⋏ (0 : SmoothForm n X l) = 0 := wedge_zero ω

theorem smoothWedge_eq_zero_of_left_eq_zero_on {k l : ℕ} (ω : SmoothForm n X k)
    (η : SmoothForm n X l) {U : Set X} (hU : IsOpen U)
    (hzero : ∀ x ∈ U, ω.as_alternating x = 0) :
    ∀ x ∈ U, (ω ⋏ η).as_alternating x = 0 := by
  intro x hx
  have hzero' : ω.as_alternating x = 0 := hzero x hx
  have hzero_wedge :
      ContinuousAlternatingMap.wedgeℂ (0 : FiberAlt n k) (η.as_alternating x) = 0 := by
    ext v
    simp [ContinuousAlternatingMap.wedgeℂ_apply, ContinuousAlternatingMap.wedgeℂ_linear]
  simp [SmoothForm.wedge_apply, hzero', hzero_wedge]

theorem smoothWedge_eq_zero_of_right_eq_zero_on {k l : ℕ} (ω : SmoothForm n X k)
    (η : SmoothForm n X l) {U : Set X} (hU : IsOpen U)
    (hzero : ∀ x ∈ U, η.as_alternating x = 0) :
    ∀ x ∈ U, (ω ⋏ η).as_alternating x = 0 := by
  intro x hx
  have hzero' : η.as_alternating x = 0 := hzero x hx
  have hzero_wedge :
      ContinuousAlternatingMap.wedgeℂ (ω.as_alternating x) (0 : FiberAlt n l) = 0 := by
    ext v
    simp [ContinuousAlternatingMap.wedgeℂ_apply, ContinuousAlternatingMap.wedgeℂ_linear]
  simp [SmoothForm.wedge_apply, hzero', hzero_wedge]

private lemma smoothWedge_eventuallyEq_zero_of_left_eventuallyEq_zero {k l : ℕ}
    (ω : SmoothForm n X k) (η : SmoothForm n X l) {x : X}
    (hzero : ω.as_alternating =ᶠ[nhds x] 0) :
    (ω ⋏ η).as_alternating =ᶠ[nhds x] 0 := by
  rcases (Filter.eventuallyEq_iff_exists_mem).1 hzero with ⟨s, hs, hEq⟩
  rcases mem_nhds_iff.mp hs with ⟨U, hUsub, hUopen, hxU⟩
  have hEqU : Set.EqOn ω.as_alternating (fun _ : X => (0 : FiberAlt n k)) U := by
    intro y hy
    exact hEq (hUsub hy)
  have hzeroU :
      ∀ y ∈ U, (ω ⋏ η).as_alternating y = 0 :=
    smoothWedge_eq_zero_of_left_eq_zero_on (ω := ω) (η := η) hUopen hEqU
  exact Filter.eventuallyEq_of_mem (hUopen.mem_nhds hxU) hzeroU

private lemma smoothWedge_eventuallyEq_zero_of_right_eventuallyEq_zero {k l : ℕ}
    (ω : SmoothForm n X k) (η : SmoothForm n X l) {x : X}
    (hzero : η.as_alternating =ᶠ[nhds x] 0) :
    (ω ⋏ η).as_alternating =ᶠ[nhds x] 0 := by
  rcases (Filter.eventuallyEq_iff_exists_mem).1 hzero with ⟨s, hs, hEq⟩
  rcases mem_nhds_iff.mp hs with ⟨U, hUsub, hUopen, hxU⟩
  have hEqU : Set.EqOn η.as_alternating (fun _ : X => (0 : FiberAlt n l)) U := by
    intro y hy
    exact hEq (hUsub hy)
  have hzeroU :
      ∀ y ∈ U, (ω ⋏ η).as_alternating y = 0 :=
    smoothWedge_eq_zero_of_right_eq_zero_on (ω := ω) (η := η) hUopen hEqU
  exact Filter.eventuallyEq_of_mem (hUopen.mem_nhds hxU) hzeroU

theorem smoothWedge_tsupport_subset_left {k l : ℕ} (ω : SmoothForm n X k)
    (η : SmoothForm n X l) :
    tsupport (ω ⋏ η).as_alternating ⊆ tsupport ω.as_alternating := by
  intro x hx
  by_contra hx'
  have hzero : ω.as_alternating =ᶠ[nhds x] 0 :=
    (notMem_tsupport_iff_eventuallyEq).1 hx'
  have hzero' :
      (ω ⋏ η).as_alternating =ᶠ[nhds x] 0 :=
    smoothWedge_eventuallyEq_zero_of_left_eventuallyEq_zero (ω := ω) (η := η) hzero
  have hxnot : x ∉ tsupport (ω ⋏ η).as_alternating :=
    (notMem_tsupport_iff_eventuallyEq).2 hzero'
  exact hxnot hx

theorem smoothWedge_tsupport_subset_right {k l : ℕ} (ω : SmoothForm n X k)
    (η : SmoothForm n X l) :
    tsupport (ω ⋏ η).as_alternating ⊆ tsupport η.as_alternating := by
  intro x hx
  by_contra hx'
  have hzero : η.as_alternating =ᶠ[nhds x] 0 :=
    (notMem_tsupport_iff_eventuallyEq).1 hx'
  have hzero' :
      (ω ⋏ η).as_alternating =ᶠ[nhds x] 0 :=
    smoothWedge_eventuallyEq_zero_of_right_eventuallyEq_zero (ω := ω) (η := η) hzero
  have hxnot : x ∉ tsupport (ω ⋏ η).as_alternating :=
    (notMem_tsupport_iff_eventuallyEq).2 hzero'
  exact hxnot hx

theorem smoothWedge_hasCompactSupport_left {k l : ℕ} (ω : SmoothForm n X k)
    (η : SmoothForm n X l) :
    HasCompactSupport ω.as_alternating →
      HasCompactSupport (ω ⋏ η).as_alternating := by
  intro hcomp
  have hcompact : IsCompact (tsupport ω.as_alternating) := by
    simpa [HasCompactSupport] using hcomp
  have hcompact' : IsCompact (tsupport (ω ⋏ η).as_alternating) :=
    IsCompact.of_isClosed_subset hcompact (isClosed_tsupport _)
      (smoothWedge_tsupport_subset_left (ω := ω) (η := η))
  simpa [HasCompactSupport] using hcompact'

theorem smoothWedge_hasCompactSupport_right {k l : ℕ} (ω : SmoothForm n X k)
    (η : SmoothForm n X l) :
    HasCompactSupport η.as_alternating →
      HasCompactSupport (ω ⋏ η).as_alternating := by
  intro hcomp
  have hcompact : IsCompact (tsupport η.as_alternating) := by
    simpa [HasCompactSupport] using hcomp
  have hcompact' : IsCompact (tsupport (ω ⋏ η).as_alternating) :=
    IsCompact.of_isClosed_subset hcompact (isClosed_tsupport _)
      (smoothWedge_tsupport_subset_right (ω := ω) (η := η))
  simpa [HasCompactSupport] using hcompact'

/-!
### Wedge with a 0-form (unit laws)

When one side is `Fin 0`, `Equiv.Perm.ModSumCongr` is a singleton, so wedging with a 0-form reduces
to scalar multiplication (up to the standard `Fin`-index cast).
-/

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
    intro i j hij
    have : σ (Sum.inr i) = σ (Sum.inr j) := by simp [hq, hij]
    exact Sum.inr_injective (σ.injective this)
  have q_surj : Function.Surjective q_fun := by
    intro j
    obtain ⟨x, hx⟩ := σ.surjective (Sum.inr j)
    rcases x with ⟨y⟩ | ⟨i⟩
    · exact (IsEmpty.false y).elim
    · refine ⟨i, ?_⟩
      have h1 : σ (Sum.inr i) = (Sum.inr j : Fin 0 ⊕ Fin l) := hx
      have h2 : σ (Sum.inr i) = (Sum.inr (q_fun i) : Fin 0 ⊕ Fin l) := hq i
      exact Sum.inr_injective (by rw [← h2, h1])
  let q : Equiv.Perm (Fin l) := Equiv.ofBijective q_fun ⟨q_inj, q_surj⟩
  refine ⟨(1, q), ?_⟩
  ext x
  rcases x with ⟨y⟩ | ⟨i⟩
  · exact (IsEmpty.false y).elim
  · simp only [Equiv.Perm.sumCongrHom_apply, Equiv.Perm.sumCongr_apply, Sum.map_inr]
    exact (hq i).symm

private instance subsingleton_modSumCongr_empty_left {l : ℕ} :
    Subsingleton (Equiv.Perm.ModSumCongr (Fin 0) (Fin l)) := by
  constructor
  intro σ₁ σ₂
  induction σ₁ using Quotient.inductionOn' with
  | h s₁ =>
    induction σ₂ using Quotient.inductionOn' with
    | h s₂ =>
      apply Quotient.sound'
      rw [QuotientGroup.leftRel_apply]
      obtain ⟨pq, hpq⟩ := sumCongrHom_surj_empty_left (l := l) (s₁⁻¹ * s₂)
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
    intro i j hij
    have : σ (Sum.inl i) = σ (Sum.inl j) := by simp [hp, hij]
    exact Sum.inl_injective (σ.injective this)
  have p_surj : Function.Surjective p_fun := by
    intro j
    obtain ⟨x, hx⟩ := σ.surjective (Sum.inl j)
    rcases x with ⟨i⟩ | ⟨y⟩
    · refine ⟨i, ?_⟩
      have h1 : σ (Sum.inl i) = (Sum.inl j : Fin k ⊕ Fin 0) := hx
      have h2 : σ (Sum.inl i) = (Sum.inl (p_fun i) : Fin k ⊕ Fin 0) := hp i
      exact Sum.inl_injective (by rw [← h2, h1])
    · exact (IsEmpty.false y).elim
  let p : Equiv.Perm (Fin k) := Equiv.ofBijective p_fun ⟨p_inj, p_surj⟩
  refine ⟨(p, 1), ?_⟩
  ext x
  rcases x with ⟨i⟩ | ⟨y⟩
  · simp only [Equiv.Perm.sumCongrHom_apply, Equiv.Perm.sumCongr_apply, Sum.map_inl]
    exact (hp i).symm
  · exact (IsEmpty.false y).elim

private instance subsingleton_modSumCongr_empty_right {k : ℕ} :
    Subsingleton (Equiv.Perm.ModSumCongr (Fin k) (Fin 0)) := by
  constructor
  intro σ₁ σ₂
  induction σ₁ using Quotient.inductionOn' with
  | h s₁ =>
    induction σ₂ using Quotient.inductionOn' with
    | h s₂ =>
      apply Quotient.sound'
      rw [QuotientGroup.leftRel_apply]
      obtain ⟨pq, hpq⟩ := sumCongrHom_surj_empty_right (k := k) (s₁⁻¹ * s₂)
      exact ⟨pq, hpq⟩

private lemma sum_subsingleton {α : Type*} [Fintype α] [Subsingleton α]
    {M : Type*} [AddCommMonoid M] (f : α → M) (a : α) : ∑ x : α, f x = f a := by
  have h : ∀ x : α, x = a := fun x => Subsingleton.elim x a
  simp only [Finset.sum_eq_single a (fun b _ hb => absurd (h b) hb)
    (fun ha => absurd (Finset.mem_univ a) ha)]

private lemma wedgeℂ_constOfIsEmpty_right {k : ℕ} (c : ℂ) (ω : FiberAlt n k) :
    ContinuousAlternatingMap.wedgeℂ (E := TangentModel n) ω
        (ContinuousAlternatingMap.constOfIsEmpty ℝ (TangentModel n) (ι := Fin 0) c) =
      (c • ω).domDomCongr (finCongr (Nat.add_zero k).symm) := by
  classical
  ext v
  simp only [ContinuousAlternatingMap.wedgeℂ_apply, ContinuousAlternatingMap.wedgeℂ_linear]
  simp only [ContinuousAlternatingMap.domDomCongr_apply, ContinuousAlternatingMap.smul_apply]
  simp only [AlternatingMap.domDomCongr_apply, LinearMap.compAlternatingMap_apply,
    AlternatingMap.domCoprod'_apply, AlternatingMap.domCoprod_apply, MultilinearMap.sum_apply]
  let σ₀ : Equiv.Perm.ModSumCongr (Fin k) (Fin 0) := ⟦1⟧
  have hsum :
      (∑ a : Equiv.Perm.ModSumCongr (Fin k) (Fin 0),
          (AlternatingMap.domCoprod.summand ω.toAlternatingMap
              (ContinuousAlternatingMap.constOfIsEmpty ℝ (TangentModel n) (ι := Fin 0) c).toAlternatingMap a)
            (v ∘ finSumFinEquiv)) =
        (AlternatingMap.domCoprod.summand ω.toAlternatingMap
            (ContinuousAlternatingMap.constOfIsEmpty ℝ (TangentModel n) (ι := Fin 0) c).toAlternatingMap σ₀)
          (v ∘ finSumFinEquiv) :=
    sum_subsingleton (f := fun a : Equiv.Perm.ModSumCongr (Fin k) (Fin 0) =>
      (AlternatingMap.domCoprod.summand ω.toAlternatingMap
        (ContinuousAlternatingMap.constOfIsEmpty ℝ (TangentModel n) (ι := Fin 0) c).toAlternatingMap a)
        (v ∘ finSumFinEquiv)) σ₀
  rw [hsum]
  simp only [AlternatingMap.domCoprod.summand]
  conv_lhs => rw [show σ₀ = ⟦1⟧ from rfl]
  simp only [Quotient.liftOn'_mk'', MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply,
    Equiv.Perm.sign_one, one_smul, LinearMap.mul'_apply, Equiv.Perm.coe_one, id_eq, Function.comp_apply]
  have h_left :
      (fun i₁ : Fin k => v (finSumFinEquiv (m := k) (n := 0) (Sum.inl i₁))) =
        (v ∘ finCongr (Nat.add_zero k).symm) := by
    funext i
    change v (finSumFinEquiv (m := k) (n := 0) (Sum.inl i)) = v (finCongr (Nat.add_zero k).symm i)
    have hidx :
        (finSumFinEquiv (m := k) (n := 0) (Sum.inl i) : Fin (k + 0)) =
          finCongr (Nat.add_zero k).symm i := by
      have hL :
          (finSumFinEquiv (m := k) (n := 0) (Sum.inl i) : Fin (k + 0)) = Fin.castAdd 0 i := by
        simpa using (finSumFinEquiv_apply_left (m := k) (n := 0) i)
      have hR : (finCongr (Nat.add_zero k).symm i : Fin (k + 0)) = Fin.castAdd 0 i := by
        simp
      exact hL.trans hR.symm
    exact congrArg v hidx
  have h_const :
      (ContinuousAlternatingMap.constOfIsEmpty ℝ (TangentModel n) (ι := Fin 0) c).toMultilinearMap
        (fun i₂ => v (finSumFinEquiv (m := k) (n := 0) (Sum.inr i₂))) = c := rfl
  rw [h_left, h_const, smul_eq_mul, mul_comm]
  rfl

private lemma wedgeℂ_constOfIsEmpty_left {l : ℕ} (c : ℂ) (η : FiberAlt n l) :
    ContinuousAlternatingMap.wedgeℂ (E := TangentModel n)
        (ContinuousAlternatingMap.constOfIsEmpty ℝ (TangentModel n) (ι := Fin 0) c) η =
      (c • η).domDomCongr (finCongr (Nat.zero_add l).symm) := by
  classical
  ext v
  simp only [ContinuousAlternatingMap.wedgeℂ_apply, ContinuousAlternatingMap.wedgeℂ_linear]
  simp only [ContinuousAlternatingMap.domDomCongr_apply, ContinuousAlternatingMap.smul_apply]
  simp only [AlternatingMap.domDomCongr_apply, LinearMap.compAlternatingMap_apply,
    AlternatingMap.domCoprod'_apply, AlternatingMap.domCoprod_apply, MultilinearMap.sum_apply]
  let σ₀ : Equiv.Perm.ModSumCongr (Fin 0) (Fin l) := ⟦1⟧
  have hsum :
      (∑ a : Equiv.Perm.ModSumCongr (Fin 0) (Fin l),
          (AlternatingMap.domCoprod.summand
              (ContinuousAlternatingMap.constOfIsEmpty ℝ (TangentModel n) (ι := Fin 0) c).toAlternatingMap
              η.toAlternatingMap a) (v ∘ finSumFinEquiv)) =
        (AlternatingMap.domCoprod.summand
            (ContinuousAlternatingMap.constOfIsEmpty ℝ (TangentModel n) (ι := Fin 0) c).toAlternatingMap
            η.toAlternatingMap σ₀) (v ∘ finSumFinEquiv) :=
    sum_subsingleton (f := fun a : Equiv.Perm.ModSumCongr (Fin 0) (Fin l) =>
      (AlternatingMap.domCoprod.summand
        (ContinuousAlternatingMap.constOfIsEmpty ℝ (TangentModel n) (ι := Fin 0) c).toAlternatingMap
        η.toAlternatingMap a) (v ∘ finSumFinEquiv)) σ₀
  rw [hsum]
  simp only [AlternatingMap.domCoprod.summand]
  conv_lhs => rw [show σ₀ = ⟦1⟧ from rfl]
  simp only [Quotient.liftOn'_mk'', MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply,
    Equiv.Perm.sign_one, one_smul, LinearMap.mul'_apply, Equiv.Perm.coe_one, id_eq, Function.comp_apply]
  have h_inputs :
      (fun i₂ : Fin l => v (finSumFinEquiv (m := 0) (n := l) (Sum.inr i₂))) =
        (v ∘ finCongr (Nat.zero_add l).symm) := by
    funext i
    change v (finSumFinEquiv (m := 0) (n := l) (Sum.inr i)) = v (finCongr (Nat.zero_add l).symm i)
    have hL :
        (finSumFinEquiv (m := 0) (n := l) (Sum.inr i) : Fin (0 + l)) = Fin.natAdd 0 i := by
      simpa using (finSumFinEquiv_apply_right (m := 0) (n := l) i)
    -- both sides are definitionally `i` in `Fin (0+l)`
    simpa [hL]
  rw [h_inputs]
  simp

/-- Wedge of unit form with any k-form gives back the k-form (up to degree cast).

For a k-form ω, the 0-form `unitForm` acts as a multiplicative unit:
- `unitForm x = constOfIsEmpty 1` (the scalar 1 as a 0-form)
- `(unitForm ⋏ ω) x = wedge (constOfIsEmpty 1) (ω x) = 1 • ω x = ω x`

The result lives in `Fin (0 + k)` which equals `Fin k` propositionally.

## References

- [Bott-Tu, "Differential Forms in Algebraic Topology", GTM 82, Ch. 1]
- [Warner, "Foundations of Differentiable Manifolds", GTM 94, Ch. 2] -/
theorem smoothWedge_unitForm_left {k : ℕ} (ω : SmoothForm n X k) :
    unitForm ⋏ ω = castForm (Nat.zero_add k).symm ω := by
  apply SmoothForm.ext
  funext x
  -- LHS: (unitForm ⋏ ω).as_alternating x = wedge (unitForm.as_alternating x) (ω.as_alternating x)
  simp only [SmoothForm.wedge_apply]
  -- unitForm.as_alternating x = constOfIsEmpty ℂ (TangentModel n) 1
  have h_unit : unitForm.as_alternating x =
      ContinuousAlternatingMap.constOfIsEmpty ℝ (TangentModel n) (ι := Fin 0) 1 := rfl
  rw [h_unit]
  -- Use the `wedgeℂ`-version of the unit law.
  rw [wedgeℂ_constOfIsEmpty_left]
  -- Now RHS: (1 • ω.as_alternating x).domDomCongr (finCongr (Nat.zero_add k).symm)
  simp only [one_smul]
  -- castForm gives h ▸ ω, and at point x: h ▸ ω.as_alternating x
  simp only [SmoothForm.castForm_as_alternating]
  -- Use castAlt_eq_transport_wedge: domDomCongr (finCongr h) = h ▸
  rw [castAlt_eq_transport_wedge]

/-- Wedge of any k-form with unit form gives back the k-form (up to degree cast).

## References

- [Bott-Tu, "Differential Forms in Algebraic Topology", GTM 82, Ch. 1]
- [Warner, "Foundations of Differentiable Manifolds", GTM 94, Ch. 2] -/
theorem smoothWedge_unitForm_right {k : ℕ} (ω : SmoothForm n X k) :
    ω ⋏ unitForm = castForm (Nat.add_zero k).symm ω := by
  apply SmoothForm.ext
  funext x
  simp only [SmoothForm.wedge_apply]
  have h_unit : unitForm.as_alternating x =
      ContinuousAlternatingMap.constOfIsEmpty ℝ (TangentModel n) (ι := Fin 0) 1 := rfl
  rw [h_unit]
  rw [wedgeℂ_constOfIsEmpty_right]
  simp only [one_smul]
  simp only [SmoothForm.castForm_as_alternating]
  rw [castAlt_eq_transport_wedge]

/-!
NOTE: smoothWedge_assoc was archived with wedge_assoc to archive/Hodge/Analytic/WedgeAssoc.lean
because it is NOT on the proof track of hodge_conjecture'.
-/

end
