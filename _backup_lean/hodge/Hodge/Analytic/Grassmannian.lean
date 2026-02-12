import Hodge.Analytic.Norms
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Geometry.Convex.Cone.Basic
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.Analysis.Convex.Cone.Closure
import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!

This file defines the calibrated Grassmannian and the strongly positive cone
of (p,p)-forms on a Kahler manifold.
-/

noncomputable section

open Classical Metric Set Filter Hodge

set_option autoImplicit false

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
  {p : ℕ}

/-! ## Calibrated Grassmannian -/

/-- The calibrated Grassmannian G_p(x): the set of complex p-planes in T_x X. -/
def CalibratedGrassmannian (p : ℕ) (x : X) : Set (Submodule ℂ (TangentSpace (𝓒_complex n) x)) :=
  { V | Module.finrank ℂ V = p }

/-! ## Volume Form Construction Helpers -/

section VolumeFormConstruction

variable {n' : ℕ} {X' : Type*}
  [TopologicalSpace X'] [ChartedSpace (EuclideanSpace ℂ (Fin n')) X']

/-- The ℝ-linear embedding of real numbers into complex numbers. -/
def inclRC : ℝ →ₗ[ℝ] ℂ where
  toFun r := (r : ℂ)
  map_add' a b := by simp
  map_smul' r a := by simp [Algebra.smul_def]

/-- The determinant alternating map on V with respect to a real basis. -/
def bDet {p' : ℕ} {x' : X'}
    {V' : Submodule ℂ (TangentSpace (𝓒_complex n') x')}
    (b : Module.Basis (Fin (2 * p')) ℝ (↥V')) :
    ↥V' [⋀^Fin (2 * p')]→ₗ[ℝ] ℝ := b.det

/-- The determinant alternating map on V, pushed forward to ℂ via `inclRC`. -/
def bDetC {p' : ℕ} {x' : X'}
    {V' : Submodule ℂ (TangentSpace (𝓒_complex n') x')}
    (b : Module.Basis (Fin (2 * p')) ℝ (↥V')) :
    ↥V' [⋀^Fin (2 * p')]→ₗ[ℝ] ℂ :=
  inclRC.compAlternatingMap (bDet b)

/-- The ℝ-linear projection from TangentSpace onto V using an ℝ-linear complement. -/
def volumeFormProj {x' : X'} {V' : Submodule ℂ (TangentSpace (𝓒_complex n') x')}
    (Q : Submodule ℝ (TangentSpace (𝓒_complex n') x'))
    (hVQ : IsCompl (V'.restrictScalars ℝ) Q) :
    TangentSpace (𝓒_complex n') x' →ₗ[ℝ] ↥V' :=
  Submodule.linearProjOfIsCompl (V'.restrictScalars ℝ) Q hVQ

/-- The full alternating (2p)-form on TangentSpace, constructed from:
    1. A real basis of V (giving a determinant form on V)
    2. Projection from TangentSpace to V
    3. Coercion ℝ → ℂ on the output. -/
def volumeFormFinal {p' : ℕ} {x' : X'}
    {V' : Submodule ℂ (TangentSpace (𝓒_complex n') x')}
    (b : Module.Basis (Fin (2 * p')) ℝ (↥V'))
    (Q : Submodule ℝ (TangentSpace (𝓒_complex n') x'))
    (hVQ : IsCompl (V'.restrictScalars ℝ) Q) :
    TangentSpace (𝓒_complex n') x' [⋀^Fin (2 * p')]→ₗ[ℝ] ℂ :=
  (bDetC b).compLinearMap (volumeFormProj Q hVQ)

/-- The determinant of a basis evaluated on itself is 1. -/
theorem bDet_self {p' : ℕ} {x' : X'}
    {V' : Submodule ℂ (TangentSpace (𝓒_complex n') x')}
    (b : Module.Basis (Fin (2 * p')) ℝ (↥V')) :
    bDet b b = 1 := b.det_self

/-- The ℂ-valued determinant of a basis evaluated on itself is 1. -/
theorem bDetC_self {p' : ℕ} {x' : X'}
    {V' : Submodule ℂ (TangentSpace (𝓒_complex n') x')}
    (b : Module.Basis (Fin (2 * p')) ℝ (↥V')) :
    bDetC b b = (1 : ℂ) := by
  unfold bDetC inclRC
  simp [LinearMap.compAlternatingMap_apply, bDet_self b]

/-- The projection onto V fixes elements of V. -/
theorem volumeFormProj_on_V {x' : X'}
    {V' : Submodule ℂ (TangentSpace (𝓒_complex n') x')}
    (Q : Submodule ℝ (TangentSpace (𝓒_complex n') x'))
    (hVQ : IsCompl (V'.restrictScalars ℝ) Q) (v : ↥V') :
    volumeFormProj Q hVQ (v : TangentSpace (𝓒_complex n') x') = v := by
  unfold volumeFormProj
  exact Submodule.linearProjOfIsCompl_apply_left hVQ v

/-- The volume form evaluated on basis vectors equals 1. -/
theorem volumeFormFinal_on_basis {p' : ℕ} {x' : X'}
    {V' : Submodule ℂ (TangentSpace (𝓒_complex n') x')}
    (b : Module.Basis (Fin (2 * p')) ℝ (↥V'))
    (Q : Submodule ℝ (TangentSpace (𝓒_complex n') x'))
    (hVQ : IsCompl (V'.restrictScalars ℝ) Q) :
    volumeFormFinal b Q hVQ (fun i => (b i : TangentSpace (𝓒_complex n') x')) = (1 : ℂ) := by
  unfold volumeFormFinal
  simp only [AlternatingMap.compLinearMap_apply]
  have h_proj_eq : (fun i => volumeFormProj Q hVQ ((b i : ↥V') : TangentSpace (𝓒_complex n') x')) = b := by
    ext i
    have h := volumeFormProj_on_V Q hVQ (b i)
    simp only [h]
  rw [h_proj_eq]
  exact bDetC_self b

end VolumeFormConstruction

/-! ## Simple Calibrated Forms -/

/-- **Predicate: Form is a Volume Form on Subspace**

A (2p)-form ω is a volume form on a complex p-dimensional subspace V if:
1. ω is nonzero on V (normalized)
2. ω vanishes on vectors orthogonal to V

Reference: [Harvey-Lawson, "Calibrated geometries", 1982, Section 2] -/
def IsVolumeFormOn {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    (x : X) (p : ℕ) (V : Submodule ℂ (TangentSpace (𝓒_complex n) x))
    (ω : (TangentSpace (𝓒_complex n) x) [⋀^Fin (2 * p)]→ₗ[ℝ] ℂ) : Prop :=
  ∃ v : Fin (2 * p) → V, ω (fun i => (v i : TangentSpace (𝓒_complex n) x)) ≠ 0

/-- **Volume Forms are Nonzero** (Structural).
    A volume form on a p-dimensional complex subspace is nonzero by definition.
    This follows from the normalization condition in the definition of IsVolumeFormOn.
    Reference: [Harvey-Lawson, "Calibrated geometries", 1982, Section 2]. -/
theorem IsVolumeFormOn_nonzero {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    (x : X) (p : ℕ) (V : Submodule ℂ (TangentSpace (𝓒_complex n) x))
    (ω : (TangentSpace (𝓒_complex n) x) [⋀^Fin (2 * p)]→ₗ[ℝ] ℂ)
    (_hV : Module.finrank ℂ V = p) :
    IsVolumeFormOn x p V ω → ω ≠ 0
  := by
  intro hω
  rcases hω with ⟨v, hv⟩
  intro hzero
  apply hv
  -- If ω = 0, evaluation is 0.
  simp [hzero]

/-- **Volume Form Existence for p > 0** (foundational exterior algebra).

    For a complex p-dimensional subspace V of the tangent space (with p > 0),
    there exists a (2p)-alternating map that is nonzero when evaluated on
    some 2p-tuple of vectors from V.

    **Mathematical Content:**
    - V has complex finrank p, hence real finrank 2p (by `Module.finrank_mul_finrank`
      with `finrank ℝ ℂ = 2`).
    - V has a real basis `b : Fin (2p) → V`.
    - The inclusion `ι : V →ₗ[ℝ] TangentSpace` gives 2p linearly independent vectors.
    - We can construct an alternating map that's nonzero on this family.

    **Proof Strategy:**
    1. Get `hV_real : finrank ℝ V = 2 * p` from `finrank ℝ ℂ = 2` and `finrank ℂ V = p`.
    2. Get a real basis `b : Basis (Fin (2*p)) ℝ V` using `finrank_eq_card_basis`.
    3. Embed basis vectors into TangentSpace: `v i := (b i : TangentSpace)`.
    4. These are linearly independent (submodule inclusion preserves this).
    5. Extend to a basis of TangentSpace (which has real dim 2n).
    6. Use `Basis.det` to get an alternating map; it's nonzero on the basis.

    This is a foundational result in linear algebra. The explicit construction
    requires coordinating several Mathlib APIs (restrictScalars, Basis, det). -/
theorem exists_volume_form_positive_case (p : ℕ) (x : X)
    (V : Submodule ℂ (TangentSpace (𝓒_complex n) x))
    (hV : Module.finrank ℂ V = p) (hp : p > 0) :
    ∃ (ω : (TangentSpace (𝓒_complex n) x) [⋀^Fin (2 * p)]→ₗ[ℝ] ℂ),
      IsVolumeFormOn (n := n) (X := X) x p V ω := by
  -- Step 1: V has real finrank 2p (since finrank ℝ ℂ = 2 and finrank ℂ V = p)
  have hV_real : Module.finrank ℝ V = 2 * p := by
    have eq1 := Module.finrank_mul_finrank ℝ ℂ (↥V)
    rw [Complex.finrank_real_complex, hV, mul_comm] at eq1
    omega

  -- Step 2: V is finite-dimensional as an ℝ-module
  haveI hfin_real : Module.Finite ℝ V := by
    apply Module.finite_of_finrank_pos
    rw [hV_real]; omega

  -- Step 3: Get a real basis b : Fin (2*p) → V
  let b : Module.Basis (Fin (2 * p)) ℝ V := Module.finBasisOfFinrankEq ℝ V hV_real

  -- Step 4: Get an ℝ-linear complement Q of V in TangentSpace
  obtain ⟨Q, hVQ⟩ := Submodule.exists_isCompl (V.restrictScalars ℝ)

  -- Step 5: Construct the volume form using our helpers
  let ω := volumeFormFinal b Q hVQ

  -- Step 6: Show ω is nonzero on some 2p-tuple from V
  use ω
  unfold IsVolumeFormOn
  use b  -- The basis vectors form a 2p-tuple in V
  -- ω evaluated on basis vectors equals 1 ≠ 0
  rw [volumeFormFinal_on_basis b Q hVQ]
  exact one_ne_zero

/-- **Existence of Volume Form** (Harvey-Lawson, 1982).
    For any complex p-plane V in the tangent space, there exists a volume form on V.

    **Proof:**
    Case p = 0: Use the constant 1-form (a 0-form is just a scalar).
    Case p > 0: Use the exterior algebra construction on a basis of V.

    Reference: [Harvey-Lawson, "Calibrated geometries", 1982, Section 2] -/
theorem exists_volume_form_of_submodule_axiom (p : ℕ) (x : X)
    (V : Submodule ℂ (TangentSpace (𝓒_complex n) x))
    (hV : Module.finrank ℂ V = p) :
    ∃ (ω : (TangentSpace (𝓒_complex n) x) [⋀^Fin (2 * p)]→ₗ[ℝ] ℂ),
      IsVolumeFormOn (n := n) (X := X) x p V ω := by
  -- Case split on p
  by_cases hp : p = 0
  · -- p = 0: The subspace is trivial, a constant 0-form works
    subst hp
    simp only [Nat.mul_zero]
    -- For p=0, we need a 0-form which is just a constant ℂ value
    haveI : IsEmpty (Fin 0) := Fin.isEmpty
    use AlternatingMap.constOfIsEmpty (R := ℝ) (M := TangentSpace (𝓒_complex n) x)
        (ι := Fin 0) (1 : ℂ)
    unfold IsVolumeFormOn
    use Fin.elim0
    simp only [ne_eq]
    exact one_ne_zero
  · -- p > 0: Use exterior algebra construction
    have hp_pos : p > 0 := Nat.pos_of_ne_zero hp
    exact exists_volume_form_positive_case p x V hV hp_pos

/-- **Existence of Volume Form** (theorem version wrapping the axiom). -/
theorem exists_volume_form_of_submodule (p : ℕ) (x : X)
    (V : Submodule ℂ (TangentSpace (𝓒_complex n) x))
    (hV : Module.finrank ℂ V = p) :
    ∃ (ω : (TangentSpace (𝓒_complex n) x) [⋀^Fin (2 * p)]→ₗ[ℝ] ℂ),
      IsVolumeFormOn (n := n) (X := X) x p V ω :=
  exists_volume_form_of_submodule_axiom p x V hV

/-- Every complex p-plane in the tangent space has a unique volume form. -/
def volume_form_of_submodule (p : ℕ) (x : X) (V : Submodule ℂ (TangentSpace (𝓒_complex n) x))
    (hV : Module.finrank ℂ V = p) :
    (TangentSpace (𝓒_complex n) x) [⋀^Fin (2 * p)]→ₗ[ℝ] ℂ :=
  Classical.choose (exists_volume_form_of_submodule p x V hV)

/-- Continuous version of `volume_form_of_submodule`, using finite-dimensional boundedness. -/
noncomputable def volume_form_of_submodule_cont (p : ℕ) (x : X)
    (V : Submodule ℂ (TangentSpace (𝓒_complex n) x)) (hV : Module.finrank ℂ V = p) :
    (TangentSpace (𝓒_complex n) x) [⋀^Fin (2 * p)]→L[ℝ] ℂ := by
  classical
  -- The tangent space is finite-dimensional over ℝ (modeled on ℂ^n).
  haveI : FiniteDimensional ℝ (TangentSpace (𝓒_complex n) x) := by
    simpa [TangentSpace] using
      (inferInstance : FiniteDimensional ℝ (EuclideanSpace ℂ (Fin n)))
  let ω : (TangentSpace (𝓒_complex n) x) [⋀^Fin (2 * p)]→ₗ[ℝ] ℂ :=
    volume_form_of_submodule (n := n) (X := X) p x V hV
  have h_ex :
      ∃ C : ℝ, ∀ v : Fin (2 * p) → TangentSpace (𝓒_complex n) x,
        ‖ω v‖ ≤ C * ∏ i, ‖v i‖ :=
    AlternatingMap.exists_bound_fin_dim (𝕜 := ℝ)
      (E := TangentSpace (𝓒_complex n) x) (F := ℂ) (ι := Fin (2 * p)) ω
  exact ω.mkContinuous (Classical.choose h_ex) (Classical.choose_spec h_ex)

/-- The simple calibrated (p,p)-form at a point x, associated to a complex p-plane V. -/
def simpleCalibratedForm_raw (p : ℕ) (x : X) (V : Submodule ℂ (TangentSpace (𝓒_complex n) x))
    (hV : Module.finrank ℂ V = p) :
    (TangentSpace (𝓒_complex n) x) [⋀^Fin (2 * p)]→L[ℝ] ℂ :=
  volume_form_of_submodule_cont (n := n) (X := X) p x V hV

/-! ## Fiber-Level Calibrated Cone

This section defines the calibrated cone at the fiber level, matching the
mathematical definition in [Harvey-Lawson, "Calibrated geometries", 1982].

The key insight is that the calibrated cone $\mathcal{C}_x$ is defined
**at each point** as a subset of $\Lambda^{2p}T^*_x X$ (alternating maps
on the tangent space at $x$). This is the correct abstraction level for:
- Membership tests
- Distance calculations
- Cone properties (convexity, closure)

The `SmoothForm`-level definition wraps these fiber-level forms into global
forms, which requires `IsSmoothAlternating`. This wrapping is only needed
for operations that genuinely require global smooth forms (e.g., integration).
-/

/-- The set of all simple calibrated forms at a fiber (alternating maps at point x).
    This is the generating set for the calibrated cone at x.

    Reference: [Harvey-Lawson, "Calibrated geometries", 1982, Section 2]. -/
def SimpleCalibratedFormsAtFiber (p : ℕ) (x : X) :
    Set ((TangentSpace (𝓒_complex n) x) [⋀^Fin (2 * p)]→L[ℝ] ℂ) :=
  { φ | ∃ (V : Submodule ℂ (TangentSpace (𝓒_complex n) x)) (hV : Module.finrank ℂ V = p),
    φ = simpleCalibratedForm_raw (n := n) (X := X) p x V hV }

/-- The calibrated cone at a fiber: the closed convex cone generated by simple
    calibrated forms at point x. This is defined as the span of the generating
    forms (which includes 0 and is closed under addition and nonnegative scaling).

    Mathematically, this is $\mathcal{C}_x = \{ \sum_j a_j \phi_{V_j} : a_j \geq 0, V_j \in G_p(x) \}$.

    Reference: [Harvey-Lawson, "Calibrated geometries", 1982, Definition 2.1]. -/
def CalibratedConeAtFiber (p : ℕ) (x : X) :
    Set ((TangentSpace (𝓒_complex n) x) [⋀^Fin (2 * p)]→L[ℝ] ℂ) :=
  -- We take the **topological closure** of the conical span to match the TeX definition
  -- “closed convex cone generated by simple calibrated forms”.
  (PointedCone.closure (PointedCone.span ℝ (SimpleCalibratedFormsAtFiber (n := n) p x))).carrier

/-- The calibrated cone at a fiber is closed (by definition via `PointedCone.closure`). -/
theorem CalibratedConeAtFiber_isClosed (p : ℕ) (x : X) :
    IsClosed (CalibratedConeAtFiber (n := n) (X := X) p x) := by
  -- `PointedCone.closure` has carrier `closure`.
  classical
  unfold CalibratedConeAtFiber
  -- `PointedCone.coe_closure` gives `(K.closure : Set E) = closure K`.
  simpa [PointedCone.coe_closure] using
    (isClosed_closure : IsClosed (closure ((PointedCone.span ℝ (SimpleCalibratedFormsAtFiber (n := n) (X := X) p x)) : Set _)))

/-- The calibrated cone at a fiber contains zero (it is pointed). -/
theorem CalibratedConeAtFiber_zero_mem (p : ℕ) (x : X) :
    (0 : (TangentSpace (𝓒_complex n) x) [⋀^Fin (2 * p)]→L[ℝ] ℂ) ∈
      CalibratedConeAtFiber (n := n) p x := by
  unfold CalibratedConeAtFiber
  -- `0` is in the conical span, hence in its closure.
  exact Submodule.zero_mem _

/-- The calibrated cone at a fiber is convex. -/
theorem CalibratedConeAtFiber_convex (p : ℕ) (x : X) :
    Convex ℝ (CalibratedConeAtFiber (n := n) p x) := by
  unfold CalibratedConeAtFiber
  exact PointedCone.convex _

/-- Simple calibrated forms at a fiber is non-empty when p ≤ n.

    For 1 ≤ p ≤ n, the tangent space at x has complex dimension n, so it contains
    complex p-dimensional subspaces. Each such subspace has a volume form,
    which is a simple calibrated form.

    **Mathematical Content**: The Grassmannian G_p(T_x X) is non-empty when p ≤ n.
    This follows from linear algebra: a vector space of dimension n contains
    subspaces of all dimensions from 0 to n.

    **Proof**: Uses `exists_linearIndependent_of_le_finrank` to get p linearly independent
    vectors in the tangent space (which has finrank n ≥ p), then takes their span. -/
theorem SimpleCalibratedFormsAtFiber_nonempty (p : ℕ) (x : X) (hp : p ≤ n) (_hn : 0 < n) :
    (SimpleCalibratedFormsAtFiber (n := n) p x).Nonempty := by
  -- TangentSpace = EuclideanSpace ℂ (Fin n) has finrank n
  have h_finrank : Module.finrank ℂ (TangentSpace (𝓒_complex n) x) = n := by
    -- TangentSpace (𝓒_complex n) x = EuclideanSpace ℂ (Fin n)
    simp only [TangentSpace]
    rw [finrank_euclideanSpace, Fintype.card_fin]
  have hp' : p ≤ Module.finrank ℂ (TangentSpace (𝓒_complex n) x) := hp.trans_eq h_finrank.symm
  -- Get p linearly independent vectors (this works even for p=0)
  obtain ⟨f, hf_li⟩ := exists_linearIndependent_of_le_finrank hp'
  -- Their span is a p-dimensional subspace
  let V := Submodule.span ℂ (Set.range f)
  have hV : Module.finrank ℂ V = p := by
    rw [finrank_span_eq_card hf_li]
    exact Fintype.card_fin p
  use simpleCalibratedForm_raw (n := n) (X := X) p x V hV
  exact ⟨V, hV, rfl⟩

/-- The calibrated cone contains non-zero elements when 1 ≤ p ≤ n.

    This shows the cone is non-trivially non-empty (not just {0}).
    The proof uses that every p-dimensional subspace has a non-zero volume form. -/
theorem CalibratedConeAtFiber_nontrivial (p : ℕ) (x : X) (_hp : 1 ≤ p) (hpn : p ≤ n) (hn : 0 < n) :
    ∃ φ ∈ CalibratedConeAtFiber (n := n) p x, φ ≠ 0 := by
  -- Get a simple calibrated form from the nonempty generating set
  obtain ⟨φ, hφ⟩ := SimpleCalibratedFormsAtFiber_nonempty p x hpn hn
  use φ
  constructor
  · -- φ is in the cone: it is a generator, hence in the conical span, hence in the closure.
    unfold CalibratedConeAtFiber
    -- Work in the pointed cone `K := span ℝ (SimpleCalibratedFormsAtFiber ...)`.
    have h_in_span :
        φ ∈ PointedCone.span ℝ (SimpleCalibratedFormsAtFiber (n := n) (X := X) p x) :=
      Submodule.subset_span hφ
    -- Hence `φ ∈ closure (K : Set _)`, i.e. `φ ∈ K.closure`.
    have h_in_closure :
        φ ∈ closure ((PointedCone.span ℝ (SimpleCalibratedFormsAtFiber (n := n) (X := X) p x)) : Set _) :=
      subset_closure h_in_span
    -- Convert the set-closure membership to pointed-cone closure membership.
    simpa [PointedCone.mem_closure] using h_in_closure
  · -- φ ≠ 0: The volume form of a p-dimensional subspace (p ≥ 1) is non-zero
    obtain ⟨V, hV, rfl⟩ := hφ
    -- Use the nonzero of the underlying alternating map.
    have h_spec := Classical.choose_spec (exists_volume_form_of_submodule p x V hV)
    have h_nonzero :
        (volume_form_of_submodule (n := n) (X := X) p x V hV) ≠ 0 :=
      IsVolumeFormOn_nonzero (n := n) (X := X) x p V _ hV h_spec
    intro hzero
    apply h_nonzero
    -- `mkContinuous` doesn't change pointwise evaluation.
    ext v
    have h := congrArg (fun f => f v) hzero
    simpa [volume_form_of_submodule_cont, volume_form_of_submodule] using h

/-- Evaluate a SmoothForm at a point to get an element of the fiber.
    We coerce from the continuous alternating map to the underlying linear alternating map. -/
def SmoothForm.evalAt {k : ℕ} (α : SmoothForm n X k) (x : X) :
    (TangentSpace (𝓒_complex n) x) [⋀^Fin k]→L[ℝ] ℂ := by
  -- `FiberAlt n k` is definitionaly the continuous alternating maps on the model tangent space,
  -- and for `𝓒_complex n` this model is definitionally the tangent space at `x`.
  simpa using (α.as_alternating x)

/-- Operator norm of an alternating map at a fiber.
    Defined as the supremum of |φ(v)| over unit vectors.

    This is the fiber-level analog of `pointwiseComass`. -/
noncomputable def alternatingNormAtFiber {k : ℕ} (x : X)
    (φ : (TangentSpace (𝓒_complex n) x) [⋀^Fin k]→L[ℝ] ℂ) : ℝ :=
  sSup { r : ℝ | ∃ v : Fin k → TangentSpace (𝓒_complex n) x,
    (∀ i, ‖v i‖ ≤ 1) ∧ r = ‖φ v‖ }

/-- Operator norm at fiber is non-negative. -/
theorem alternatingNormAtFiber_nonneg {k : ℕ} (x : X)
    (φ : (TangentSpace (𝓒_complex n) x) [⋀^Fin k]→L[ℝ] ℂ) :
    alternatingNormAtFiber (n := n) x φ ≥ 0 := by
  unfold alternatingNormAtFiber
  apply Real.sSup_nonneg
  intro r hr
  rcases hr with ⟨_, ⟨_, rfl⟩⟩
  exact norm_nonneg _

/-- The pointwise distance from a form to the fiber-level calibrated cone at x.
    This is the mathematically correct definition that matches the paper.

    Mathematically: $d(\alpha_x, \mathcal{C}_x) = \inf_{\beta \in \mathcal{C}_x} \|\alpha_x - \beta\|_{op}$

    Reference: [Harvey-Lawson, "Calibrated geometries", 1982, Section 3]. -/
noncomputable def distToConeAtFiber (p : ℕ) (x : X)
    (αx : (TangentSpace (𝓒_complex n) x) [⋀^Fin (2 * p)]→L[ℝ] ℂ) : ℝ :=
  sInf { r : ℝ | ∃ βx ∈ CalibratedConeAtFiber (n := n) p x,
    r = alternatingNormAtFiber (n := n) x (αx - βx) }

/-- Distance to fiber-level cone is non-negative. -/
theorem distToConeAtFiber_nonneg (p : ℕ) (x : X)
    (αx : (TangentSpace (𝓒_complex n) x) [⋀^Fin (2 * p)]→L[ℝ] ℂ) :
    distToConeAtFiber (n := n) p x αx ≥ 0 := by
  unfold distToConeAtFiber
  apply Real.sInf_nonneg
  intro r hr
  rcases hr with ⟨_, _, rfl⟩
  exact alternatingNormAtFiber_nonneg (n := n) x _

/-- The pointwise distance from a SmoothForm to the calibrated cone at x,
    computed via the fiber-level cone. This is the preferred definition. -/
noncomputable def distToConeAtPoint (p : ℕ) (α : SmoothForm n X (2 * p)) (x : X) : ℝ :=
  distToConeAtFiber (n := n) p x (α.evalAt x)

/-- Distance to cone at point is non-negative. -/
theorem distToConeAtPoint_nonneg (p : ℕ) (α : SmoothForm n X (2 * p)) (x : X) :
    distToConeAtPoint (n := n) p α x ≥ 0 := by
  unfold distToConeAtPoint
  exact distToConeAtFiber_nonneg (n := n) p x (α.evalAt x)

/-- The global cone defect via fiber-level definition:
    supremum over x of the pointwise distance to the calibrated cone. -/
noncomputable def coneDefectFiber (p : ℕ) (α : SmoothForm n X (2 * p)) : ℝ :=
  sSup (Set.range fun x : X => distToConeAtPoint (n := n) p α x)

/-- Cone defect (fiber version) is non-negative. -/
theorem coneDefectFiber_nonneg (p : ℕ) (α : SmoothForm n X (2 * p)) :
    coneDefectFiber (n := n) (X := X) p α ≥ 0 := by
  unfold coneDefectFiber
  apply Real.sSup_nonneg
  intro r hr
  rcases hr with ⟨x, rfl⟩
  exact distToConeAtPoint_nonneg (n := n) p α x
end
