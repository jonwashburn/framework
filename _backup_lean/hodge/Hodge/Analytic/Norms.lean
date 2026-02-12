import Hodge.Kahler.Manifolds
import Hodge.Analytic.HodgeStar.FiberStar
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Topology.Order.Monotone
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Algebra.Support

/-!
# Track B.2: Norms and Metrics

This file defines the global norms on differential forms (comass and L2)
and proves their basic properties on compact Kähler manifolds.

We define the pointwise comass as the operator norm of the alternating map,
and the global comass as its supremum over the manifold.
-/

noncomputable section

open Classical Set Filter Hodge
open scoped Pointwise

set_option autoImplicit false

/-- Pointwise comass of a k-form at a point x.
    Defined as the operator norm `‖α(x)‖` in the normed space of continuous alternating maps.

    This matches the manuscript definition (sup over the unit ball) because the norm on
    `ContinuousAlternatingMap` is the operator norm. -/
noncomputable def pointwiseComass {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    {k : ℕ} (α : SmoothForm n X k) (x : X) : ℝ :=
  ‖α.as_alternating x‖

/-! ### Pointwise Comass Properties -/

/-- **Pointwise Comass Non-negativity**. -/
theorem pointwiseComass_nonneg {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    {k : ℕ} (α : SmoothForm n X k) (x : X) : pointwiseComass α x ≥ 0 := by
  simpa [pointwiseComass] using (norm_nonneg (α.as_alternating x))

/-- **Pointwise Comass of Zero**.
    The zero form has zero comass at every point. -/
theorem pointwiseComass_zero {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [HasLocallyConstantCharts n X]
    (x : X) {k : ℕ} : pointwiseComass (0 : SmoothForm n X k) x = 0 := by
  simp [pointwiseComass]

/-- **Pointwise Comass Triangle Inequality**. -/
theorem pointwiseComass_add_le {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [HasLocallyConstantCharts n X]
    {k : ℕ} (α β : SmoothForm n X k) (x : X) :
    pointwiseComass (α + β) x ≤ pointwiseComass α x + pointwiseComass β x := by
  simpa [pointwiseComass, SmoothForm.add_apply] using
    (norm_add_le (α.as_alternating x) (β.as_alternating x))

/-- **Pointwise Comass Homogeneity**.
    The operator norm scales by absolute value. -/
theorem pointwiseComass_smul {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    {k : ℕ} (r : ℝ) (α : SmoothForm n X k) (x : X) :
    pointwiseComass (r • α) x = |r| * pointwiseComass α x
  := by
  simp [pointwiseComass, norm_smul]

/-- **Negation as Scalar Multiplication** (Derived from Module structure). -/
theorem SmoothForm.neg_eq_neg_one_smul {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    {k : ℕ} (α : SmoothForm n X k) : (-α) = (-1 : ℝ) • α := by
  rw [neg_one_smul]

theorem pointwiseComass_neg {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    {k : ℕ} (α : SmoothForm n X k) (x : X) :
    pointwiseComass (-α) x = pointwiseComass α x := by
  rw [SmoothForm.neg_eq_neg_one_smul, pointwiseComass_smul]
  simp

/-- **Pointwise Comass is Continuous** (Now a Theorem!).
    The pointwise comass (operator norm) of a smooth form varies continuously.

    **Proof**: By definition of `IsSmoothAlternating`, a smooth form α has continuous
    pointwise operator norm. The `pointwiseComass` function is exactly this operator norm,
    so continuity follows directly from the smoothness of α.

    **Mathematical Justification**: This follows from:
    1. Smoothness implies continuity [Lee, "Intro to Smooth Manifolds", Prop 2.3]
    2. Operator norm is continuous on finite-dimensional spaces [Rudin, "Functional Analysis", Thm 1.32]
    3. Local trivialization of tangent bundle [Voisin, "Hodge Theory I", §3.1]

    Reference: [C. Voisin, "Hodge Theory and Complex Algebraic Geometry I", 2002, Section 3.1]. -/
theorem pointwiseComass_continuous {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) : Continuous (pointwiseComass α) := by
  -- `pointwiseComass α` is `x ↦ ‖α.as_alternating x‖`.
  -- α.is_smooth : ContMDiff → continuous, and norm is continuous.
  exact continuous_norm.comp α.is_smooth.continuous

/-- Global comass norm on forms: supremum of pointwise comass. -/
def comass {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [CompactSpace X]
    {k : ℕ} (α : SmoothForm n X k) : ℝ :=
  sSup (range (pointwiseComass α))

/-- **Comass Nonnegativity**: Comass is always nonneg (supremum of nonneg values). -/
theorem comass_nonneg {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [CompactSpace X]
    {k : ℕ} (α : SmoothForm n X k) : comass α ≥ 0 := by
  unfold comass
  apply Real.sSup_nonneg
  intro r hr
  obtain ⟨x, hx⟩ := hr
  rw [← hx]
  exact pointwiseComass_nonneg α x

-- comass_eq_zero_iff removed (unused)
-- Definiteness would require proper norm setup
theorem comass_eq_zero_of_zero {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [CompactSpace X] [Nonempty X]
    {k : ℕ} : comass (0 : SmoothForm n X k) = 0 := by
  unfold comass
  have h_set : range (pointwiseComass (0 : SmoothForm n X k)) = {0} := by
    ext r
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · intro ⟨x, hx⟩
      rw [← hx, pointwiseComass_zero]
    · intro hr
      use Classical.arbitrary X
      rw [hr, pointwiseComass_zero]
  rw [h_set]
  simp only [csSup_singleton]

-- Original axiom (removed): comass_eq_zero_iff : comass α = 0 ↔ α = 0

/-- Instance: Norm on Smooth Forms using Comass. -/
instance instNormSmoothForm {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [CompactSpace X] {k : ℕ} :
    Norm (SmoothForm n X k) := ⟨comass⟩

/-- Global comass is bounded above on compact manifolds. -/
theorem comass_bddAbove {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) :
    BddAbove (range (pointwiseComass α)) := by
  apply IsCompact.bddAbove
  apply isCompact_range
  exact pointwiseComass_continuous α

/-- The comass of the zero form is zero. -/
theorem comass_zero {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [CompactSpace X] [Nonempty X]
    {k : ℕ} : comass (n := n) (0 : SmoothForm n X k) = 0 := by
  unfold comass
  have h : range (pointwiseComass (0 : SmoothForm n X k)) = {0} := by
    ext r
    simp only [mem_range, mem_singleton_iff]
    constructor
    · intro ⟨x, hx⟩; rw [pointwiseComass_zero] at hx; exact hx.symm
    · intro hr; obtain ⟨x⟩ : Nonempty X := inferInstance; use x; rw [hr, pointwiseComass_zero]
  rw [h]
  exact csSup_singleton 0

/-- Global comass satisfies triangle inequality. -/
theorem comass_add_le {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [Nonempty X]
    {k : ℕ} (α β : SmoothForm n X k) :
    comass (α + β) ≤ comass α + comass β := by
  unfold comass
  apply csSup_le
  · exact range_nonempty _
  · intro r ⟨x, hx⟩
    rw [← hx]
    calc pointwiseComass (α + β) x
        ≤ pointwiseComass α x + pointwiseComass β x := pointwiseComass_add_le α β x
      _ ≤ sSup (range (pointwiseComass α)) + sSup (range (pointwiseComass β)) := by
          apply add_le_add
          · apply le_csSup (comass_bddAbove α)
            exact mem_range_self x
          · apply le_csSup (comass_bddAbove β)
            exact mem_range_self x

/-- Comass scales with absolute value of scalar: comass(c • ω) = |c| * comass(ω).
    **BLOCKER**: Depends on `pointwiseComass_smul` and set algebra. -/
theorem comass_smul {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [CompactSpace X] [Nonempty X]
    {k : ℕ} (c : ℝ) (ω : SmoothForm n X k) : comass (c • ω) = |c| * comass ω
  := by
  unfold comass
  -- Rewrite the range using the pointwise scaling lemma.
  have h_range :
      range (pointwiseComass (c • ω)) = (|c|) • range (pointwiseComass ω) := by
    ext t
    constructor
    · rintro ⟨x, rfl⟩
      -- `t = pointwiseComass (c • ω) x`
      refine ⟨pointwiseComass ω x, ?_, ?_⟩
      · exact ⟨x, rfl⟩
      · simp [pointwiseComass_smul]
    · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
      -- `t = |c| * pointwiseComass ω x`
      refine ⟨x, ?_⟩
      simp [pointwiseComass_smul]
  rw [h_range]
  -- Apply the general `sSup` scaling lemma.
  rw [Real.sSup_smul_of_nonneg (abs_nonneg c) (range (pointwiseComass ω)), smul_eq_mul]

/-! ## Seminormed structure on Smooth Forms (comass)

We now equip `SmoothForm n X k` with the **seminormed** structure coming from the global comass
seminorm:

`‖ω‖ := comass ω`.

This upgrades the old “discrete topology placeholder” to the topology induced by the comass
pseudometric.

Note: comass is only a *seminorm* (we deliberately do not assume definiteness
`comass ω = 0 → ω = 0`), so we provide `SeminormedAddCommGroup`, not `NormedAddCommGroup`.
-/

instance instSeminormedAddCommGroupSmoothForm {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    {k : ℕ} : SeminormedAddCommGroup (SmoothForm n X k) := by
  classical
  -- `SeminormedAddCommGroup.ofCore` builds the pseudometric from a seminorm core.
  refine SeminormedAddCommGroup.ofCore (𝕜 := ℝ) (E := SmoothForm n X k)
    { norm_nonneg := fun ω => by
        -- `‖ω‖` is definitional `comass ω`
        simpa using (comass_nonneg (n := n) (X := X) (k := k) ω)
      norm_smul := fun r ω => by
        -- comass(r • ω) = |r| * comass(ω) = ‖r‖ * ‖ω‖
        simpa [Real.norm_eq_abs] using
          (comass_smul (n := n) (X := X) (k := k) (c := r) ω)
      norm_triangle := fun ω η => by
        simpa using (comass_add_le (n := n) (X := X) (k := k) ω η) }

instance instNormedSpaceRealSmoothForm {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    {k : ℕ} : NormedSpace ℝ (SmoothForm n X k) where
  norm_smul_le r ω := by
    -- We have equality from `comass_smul`, so the ≤-bound is immediate.
    simpa [Real.norm_eq_abs] using
      (le_of_eq (comass_smul (n := n) (X := X) (k := k) (c := r) ω))

/-! ## L2 Inner Product (Agent 3 - Riemannian/Kähler Infrastructure)

### Mathematical Background

On a Kähler manifold (X, ω, J), the Kähler form ω and complex structure J induce a
Riemannian metric g on the tangent bundle:

  g(v, w) = ω(v, Jw)

This metric extends to differential forms via the induced inner product on exterior powers:

  ⟨α, β⟩_x = sum over multi-indices I of g^{i₁j₁}...g^{iₖjₖ} α_I(x) β_J(x)

The global L2 inner product is then:

  ⟨α, β⟩_{L²} = ∫_X ⟨α, β⟩_x · ω^n

### Implementation Strategy (Agent 3, 2026-01-12)

We define a `KahlerMetricData` structure that bundles:
1. The pointwise inner product function on k-forms
2. Key properties (positivity, symmetry, bilinearity)
3. Volume integration for L2 inner product

This allows us to:
- Keep the proof architecture correct with properties we can use
- Replace stubs with real implementations once Agent 5 provides integration infrastructure

**References**:
- [Warner, "Foundations of Differentiable Manifolds", GTM 94, §6.1]
- [Voisin, "Hodge Theory and Complex Algebraic Geometry I", §5.1-5.2]
-/

/-- **Kähler Metric Data** (Agent 3).

    Bundles the pointwise inner product on differential forms induced by the Kähler metric,
    along with key properties needed for Hodge theory.

    The Kähler form ω and complex structure J induce a Riemannian metric g(v,w) = ω(v, Jw).
    This extends to k-forms via the metric on exterior powers of the cotangent bundle. -/
structure KahlerMetricData (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] where
  /-- Pointwise inner product of two k-forms at a point. -/
  inner : SmoothForm n X k → SmoothForm n X k → X → ℝ
  /-- Positivity: ⟨α, α⟩_x ≥ 0 -/
  inner_self_nonneg : ∀ (α : SmoothForm n X k) (x : X), inner α α x ≥ 0
  /-- Symmetry: ⟨α, β⟩_x = ⟨β, α⟩_x -/
  inner_comm : ∀ (α β : SmoothForm n X k) (x : X), inner α β x = inner β α x
  /-- Left additivity: ⟨α₁ + α₂, β⟩_x = ⟨α₁, β⟩_x + ⟨α₂, β⟩_x -/
  inner_add_left : ∀ (α₁ α₂ β : SmoothForm n X k) (x : X),
    inner (α₁ + α₂) β x = inner α₁ β x + inner α₂ β x
  /-- Scalar linearity: ⟨r • α, β⟩_x = r * ⟨α, β⟩_x -/
  inner_smul_left : ∀ (r : ℝ) (α β : SmoothForm n X k) (x : X),
    inner (r • α) β x = r * inner α β x
  /-- Continuity: the inner product varies continuously in x -/
  inner_continuous : ∀ (α β : SmoothForm n X k), Continuous (inner α β)

/-- Standard basis vector in the tangent model space (for inner products). -/
noncomputable def innerProdBasisVector (n : ℕ) (i : Fin n) : TangentModel n :=
  EuclideanSpace.single i (1 : ℂ)

/-- A standard frame of k vectors for evaluating k-forms in inner products.
    Uses the first k basis vectors (cyclically if k > n). -/
noncomputable def innerProdFrame (n k : ℕ) : Fin k → TangentModel n :=
  fun i =>
    if hn : n = 0 then 0
    else innerProdBasisVector n ⟨i.val % n, Nat.mod_lt i.val (Nat.pos_of_ne_zero hn)⟩

/-- **Real Kähler Metric Data** via fiber inner product.

    Uses the fiber-level inner product `fiberAltInner` to define pointwise inner
    products on k-forms. For forms α, β, at point x:

      ⟨α, β⟩_x = Re(fiberAltInner n k (α x) (β x))

    **Mathematical Justification**: The fiber inner product sums over all k-element
    subsets I of {0,...,n-1}:
      fiberAltInner(α, β) = Σ_{|I|=k} α(e_I) * conj(β(e_I))

    This is the standard L² inner product on Λ^k induced by the Euclidean metric.

    **Reference**: [Warner, GTM 94, §6.1], [Voisin, "Hodge Theory I", §5.1] -/
noncomputable def KahlerMetricData.fromFrame (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] : KahlerMetricData n X k where
  inner := fun α β x => (fiberAltInner n k (α.as_alternating x) (β.as_alternating x)).re
  inner_self_nonneg := fun α x => fiberAltInner_self_nonneg n k (α.as_alternating x)
  inner_comm := fun α β x => by
    have h := fiberAltInner_conj_symm n k (α.as_alternating x) (β.as_alternating x)
    -- fiberAltInner α β = conj(fiberAltInner β α)
    -- So Re(fiberAltInner α β) = Re(conj(fiberAltInner β α)) = Re(fiberAltInner β α)
    calc (fiberAltInner n k (α.as_alternating x) (β.as_alternating x)).re
      _ = (starRingEnd ℂ (fiberAltInner n k (β.as_alternating x) (α.as_alternating x))).re := by rw [h]
      _ = (star (fiberAltInner n k (β.as_alternating x) (α.as_alternating x))).re := by rfl
      _ = (fiberAltInner n k (β.as_alternating x) (α.as_alternating x)).re := Complex.conj_re _
  inner_add_left := fun α₁ α₂ β x => by
    show (fiberAltInner n k ((α₁ + α₂).as_alternating x) (β.as_alternating x)).re = _
    rw [SmoothForm.add_apply, fiberAltInner_add_left, Complex.add_re]
  inner_smul_left := fun r α β x => by
    show (fiberAltInner n k ((r • α).as_alternating x) (β.as_alternating x)).re = _
    -- r • α at fiber level becomes (↑r : ℂ) • (α x)
    have eq1 : (r • α).as_alternating x = (r : ℂ) • α.as_alternating x := by
      rw [SmoothForm.smul_real_apply]; rfl
    rw [eq1, fiberAltInner_smul_left]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, MulZeroClass.zero_mul]
    ring
  inner_continuous := fun α β => by
    -- The inner product at x is Re(fiberAltInner (α x) (β x))
    -- This is continuous because α and β are smooth (hence continuous)
    -- and fiberAltInner is a finite sum of products of continuous functions
    apply Complex.continuous_re.comp
    apply continuous_finset_sum
    intro s _
    apply Continuous.mul
    -- α.as_alternating : X → FiberAlt n k is continuous, and evaluation is continuous
    · have hα : Continuous α.as_alternating := α.is_smooth.continuous
      exact (continuous_eval_const (fiberFrame n k s)).comp hα
    · apply Complex.continuous_conj.comp
      have hβ : Continuous β.as_alternating := β.is_smooth.continuous
      exact (continuous_eval_const (fiberFrame n k s)).comp hβ

/-- **Volume Integration Data** (Agent 3).

    Bundles the volume form integration for L2 inner products.
    On a Kähler manifold of dimension n, the volume form is ω^n / n!

    The L2 inner product is: ⟨α, β⟩_{L²} = ∫_X ⟨α, β⟩_x dV -/
class VolumeIntegrationData (n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] where
  /-- Integration of a continuous real-valued function against the volume form. -/
  integrate : ContinuousMap X ℝ → ℝ
  /-- Linearity: ∫(f + g) = ∫f + ∫g -/
  integrate_add : ∀ (f g : ContinuousMap X ℝ), integrate (f + g) = integrate f + integrate g
  /-- Scalar: ∫(c · f) = c · ∫f -/
  integrate_smul : ∀ (c : ℝ) (f : ContinuousMap X ℝ), integrate (c • f) = c * integrate f
  /-- Positivity: f ≥ 0 pointwise implies ∫f ≥ 0 -/
  integrate_nonneg : ∀ (f : ContinuousMap X ℝ), (∀ x, f x ≥ 0) → integrate f ≥ 0

/-! ### Pointwise Inner Product -/

/-- Pointwise inner product of differential forms.

    Uses the Kähler metric to define ⟨α, β⟩_x at each point x.
    Implemented via frame evaluation: ⟨α, β⟩_x = Re(α(frame) · conj(β(frame))).

    **Mathematical Definition**: For a Kähler manifold with metric g induced by ω and J,
    the pointwise inner product on k-forms is:
      ⟨α, β⟩_x = sum_{|I|=k} g^{I,J}(x) α_I(x) β_J(x)
    where g^{I,J} is the induced metric on Λ^k T*_x X.

    **Reference**: [Warner, GTM 94, §6.1], [Voisin, "Hodge Theory I", §5.1] -/
noncomputable def pointwiseInner {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α β : SmoothForm n X k) (x : X) : ℝ :=
  (KahlerMetricData.fromFrame n X k).inner α β x

/-- Pointwise inner product as a continuous map. -/
noncomputable def pointwiseInner_continuousMap {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α β : SmoothForm n X k) : ContinuousMap X ℝ :=
  ⟨pointwiseInner (n := n) (X := X) (k := k) α β,
    (KahlerMetricData.fromFrame n X k).inner_continuous α β⟩

/-- **Pointwise Inner Product Positivity**. -/
theorem pointwiseInner_self_nonneg {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) (x : X) :
    pointwiseInner α α x ≥ 0 :=
  (KahlerMetricData.fromFrame n X k).inner_self_nonneg α x

/-- Pointwise norm induced by the inner product. -/
def pointwiseNorm {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) (x : X) : ℝ :=
  Real.sqrt (pointwiseInner α α x)

/-! ### Global L2 Inner Product -/

/-- Global L2 inner product of two k-forms.

    Defined as: ⟨α, β⟩_{L²} = ∫_X ⟨α, β⟩_x dV

    where dV = ω^n / n! is the volume form on the Kähler manifold.

  **Implementation**: Delegates to the explicit `VolumeIntegrationData` interface,
  which should be instantiated by genuine volume integration.

    **Reference**: [Voisin, "Hodge Theory I", §5.2] -/
noncomputable def L2Inner {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [VolumeIntegrationData n X]
    {k : ℕ} (α β : SmoothForm n X k) : ℝ :=
  (VolumeIntegrationData.integrate (n := n) (X := X))
    (pointwiseInner_continuousMap (n := n) (X := X) (k := k) α β)

/-- **L2 Inner Product Left Additivity**. -/
theorem L2Inner_add_left {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [VolumeIntegrationData n X]
    {k : ℕ} (α₁ α₂ β : SmoothForm n X k) :
    L2Inner (α₁ + α₂) β = L2Inner α₁ β + L2Inner α₂ β := by
  have hsum :
      pointwiseInner_continuousMap (n := n) (X := X) (k := k) (α₁ + α₂) β =
        pointwiseInner_continuousMap (n := n) (X := X) (k := k) α₁ β +
        pointwiseInner_continuousMap (n := n) (X := X) (k := k) α₂ β := by
    ext x
    -- Use inner_add_left from KahlerMetricData
    simpa [pointwiseInner_continuousMap, pointwiseInner, KahlerMetricData.fromFrame, Pi.add_apply] using
      (KahlerMetricData.fromFrame n X k).inner_add_left α₁ α₂ β x
  have hlin :=
    (VolumeIntegrationData.integrate_add (n := n) (X := X)
      (f := pointwiseInner_continuousMap (n := n) (X := X) (k := k) α₁ β)
      (g := pointwiseInner_continuousMap (n := n) (X := X) (k := k) α₂ β))
  -- Rewrite via the continuous-map identity and apply linearity.
  calc
    L2Inner (α₁ + α₂) β =
        (VolumeIntegrationData.integrate (n := n) (X := X))
          (pointwiseInner_continuousMap (n := n) (X := X) (k := k) (α₁ + α₂) β) := rfl
    _ = (VolumeIntegrationData.integrate (n := n) (X := X))
          (pointwiseInner_continuousMap (n := n) (X := X) (k := k) α₁ β +
            pointwiseInner_continuousMap (n := n) (X := X) (k := k) α₂ β) := by
          simpa [hsum]
    _ = (VolumeIntegrationData.integrate (n := n) (X := X))
          (pointwiseInner_continuousMap (n := n) (X := X) (k := k) α₁ β) +
        (VolumeIntegrationData.integrate (n := n) (X := X))
          (pointwiseInner_continuousMap (n := n) (X := X) (k := k) α₂ β) := hlin
    _ = L2Inner α₁ β + L2Inner α₂ β := rfl

/-- **L2 Inner Product Scalar Left Linearity**. -/
theorem L2Inner_smul_left {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [VolumeIntegrationData n X]
    {k : ℕ} (r : ℝ) (α β : SmoothForm n X k) :
    L2Inner (r • α) β = r * L2Inner α β := by
  have hsmul :
      pointwiseInner_continuousMap (n := n) (X := X) (k := k) (r • α) β =
        r • pointwiseInner_continuousMap (n := n) (X := X) (k := k) α β := by
    ext x
    simpa [pointwiseInner_continuousMap, pointwiseInner, KahlerMetricData.fromFrame,
      Pi.smul_apply, smul_eq_mul] using
      (KahlerMetricData.fromFrame n X k).inner_smul_left r α β x
  have hlin :=
    (VolumeIntegrationData.integrate_smul (n := n) (X := X) r
      (pointwiseInner_continuousMap (n := n) (X := X) (k := k) α β))
  calc
    L2Inner (r • α) β =
        (VolumeIntegrationData.integrate (n := n) (X := X))
          (pointwiseInner_continuousMap (n := n) (X := X) (k := k) (r • α) β) := rfl
    _ = (VolumeIntegrationData.integrate (n := n) (X := X))
          (r • pointwiseInner_continuousMap (n := n) (X := X) (k := k) α β) := by
          simpa [hsmul]
    _ = r *
        (VolumeIntegrationData.integrate (n := n) (X := X))
          (pointwiseInner_continuousMap (n := n) (X := X) (k := k) α β) := hlin
    _ = r * L2Inner α β := rfl

/-- **L2 Inner Product Positivity**. -/
theorem L2Inner_self_nonneg {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [VolumeIntegrationData n X]
    {k : ℕ} (α : SmoothForm n X k) :
    L2Inner α α ≥ 0 := by
  have hnonneg : ∀ x, pointwiseInner (n := n) (X := X) (k := k) α α x ≥ 0 := by
    intro x
    exact pointwiseInner_self_nonneg (n := n) (X := X) (k := k) α x
  simpa [L2Inner] using
    (VolumeIntegrationData.integrate_nonneg (n := n) (X := X)
      (pointwiseInner_continuousMap (n := n) (X := X) (k := k) α α) hnonneg)

/-- Global L2 norm of a k-form. -/
def L2NormForm {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [VolumeIntegrationData n X]
    {k : ℕ} (α : SmoothForm n X k) : ℝ :=
  Real.sqrt (L2Inner α α)

/-! ## Energy Functional -/

/-- The energy of a form is the L2 norm squared. -/
def energy {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [VolumeIntegrationData n X]
    {k : ℕ} (α : SmoothForm n X k) : ℝ := L2Inner α α

/-! **Cohomology class representatives** (definitional). -/
theorem energy_minimizer_trivial {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    (k : ℕ) (c : DeRhamCohomologyClass n X k) :
    ∃ ω : SmoothForm n X k, ∃ h : IsFormClosed ω, ⟦ω, h⟧ = c := by
  induction c using Quotient.ind with
  | _ cf =>
    use cf.1, cf.2
    rfl


-- trace_L2_control removed (unused)
-- Would state: ∃ C > 0, comass α ≤ C * L2NormForm α

/-! ## Derived Theorems -/

theorem L2NormForm_nonneg {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [VolumeIntegrationData n X]
    {k : ℕ} (α : SmoothForm n X k) : L2NormForm α ≥ 0 := Real.sqrt_nonneg _

theorem pointwiseNorm_nonneg {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) (x : X) : pointwiseNorm α x ≥ 0 := Real.sqrt_nonneg _

theorem energy_nonneg {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [VolumeIntegrationData n X]
    {k : ℕ} (α : SmoothForm n X k) : energy α ≥ 0 := L2Inner_self_nonneg α

theorem L2NormForm_sq_eq_energy {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [VolumeIntegrationData n X]
    {k : ℕ} (α : SmoothForm n X k) : (L2NormForm α) ^ 2 = energy α := by
  unfold L2NormForm energy; rw [Real.sq_sqrt (L2Inner_self_nonneg α)]

theorem pointwiseInner_comm {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α β : SmoothForm n X k) (x : X) :
    pointwiseInner α β x = pointwiseInner β α x :=
  (KahlerMetricData.fromFrame n X k).inner_comm α β x

theorem L2Inner_comm {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [VolumeIntegrationData n X]
    {k : ℕ} (α β : SmoothForm n X k) :
    L2Inner α β = L2Inner β α := by
  -- pointwiseInner α β = pointwiseInner β α by symmetry
  have h :
      pointwiseInner_continuousMap (n := n) (X := X) (k := k) α β =
        pointwiseInner_continuousMap (n := n) (X := X) (k := k) β α := by
    ext x
    exact pointwiseInner_comm (n := n) (X := X) (k := k) α β x
  simp [L2Inner, h]

theorem L2Inner_add_right {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [VolumeIntegrationData n X]
    {k : ℕ} (α β₁ β₂ : SmoothForm n X k) :
    L2Inner α (β₁ + β₂) = L2Inner α β₁ + L2Inner α β₂ := by
  rw [L2Inner_comm α (β₁ + β₂), L2Inner_add_left, L2Inner_comm β₁ α, L2Inner_comm β₂ α]

theorem L2Inner_smul_right {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [VolumeIntegrationData n X]
    {k : ℕ} (r : ℝ) (α β : SmoothForm n X k) :
    L2Inner α (r • β) = r * L2Inner α β := by
  rw [L2Inner_comm α (r • β), L2Inner_smul_left, L2Inner_comm β α]

class L2InnerCauchySchwarzData (n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [VolumeIntegrationData n X] : Prop where
  cauchy_schwarz :
    ∀ {k : ℕ} (α β : SmoothForm n X k),
      (L2Inner α β) ^ 2 ≤ (L2Inner α α) * (L2Inner β β)

theorem L2Inner_cauchy_schwarz {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [VolumeIntegrationData n X] [L2InnerCauchySchwarzData n X]
    {k : ℕ} (α β : SmoothForm n X k) :
    (L2Inner α β) ^ 2 ≤ (L2Inner α α) * (L2Inner β β) :=
  L2InnerCauchySchwarzData.cauchy_schwarz (n := n) (X := X) (k := k) α β

theorem L2NormForm_add_le {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [VolumeIntegrationData n X]
    [L2InnerCauchySchwarzData n X] {k : ℕ} (α β : SmoothForm n X k) :
    L2NormForm (α + β) ≤ L2NormForm α + L2NormForm β := by
  unfold L2NormForm
  rw [Real.sqrt_le_left (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  rw [L2Inner_add_left, L2Inner_add_right, L2Inner_add_right]
  rw [L2Inner_comm β α]
  rw [add_sq, Real.sq_sqrt (L2Inner_self_nonneg α), Real.sq_sqrt (L2Inner_self_nonneg β)]
  ring_nf
  have cs := L2Inner_cauchy_schwarz α β
  have key : L2Inner α β ≤ Real.sqrt (L2Inner α α) * Real.sqrt (L2Inner β β) := by
    rw [← Real.sqrt_mul (L2Inner_self_nonneg α)]
    apply Real.le_sqrt_of_sq_le; exact cs
  linarith

theorem L2NormForm_smul {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [VolumeIntegrationData n X]
    {k : ℕ} (r : ℝ) (α : SmoothForm n X k) :
    L2NormForm (r • α) = |r| * L2NormForm α := by
  unfold L2NormForm; rw [L2Inner_smul_left, L2Inner_smul_right]
  rw [← _root_.mul_assoc, show r * r = r ^ 2 from sq r ▸ rfl]
  rw [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs]

/-! ## Hodge Star Operator (Agent 3 - 2026-01-12)

### Mathematical Background

The **Hodge star operator** ⋆ is a fundamental operation on differential forms on
Riemannian (or Kähler) manifolds. For a 2n-dimensional Kähler manifold X:

  ⋆ : Ω^k(X) → Ω^(2n-k)(X)

The Hodge star is defined by the relation:
  α ∧ ⋆β = ⟨α, β⟩_x · vol_X

where ⟨·, ·⟩_x is the pointwise inner product and vol_X = ω^n / n! is the volume form.

### Key Properties

1. **Linearity**: ⋆(α + β) = ⋆α + ⋆β, ⋆(cα) = c·⋆α
2. **Involution**: ⋆⋆α = (-1)^{k(2n-k)} α
3. **L2 inner product**: ⟨α, β⟩_{L²} = ∫_X α ∧ ⋆β
4. **Kähler type**: On a Kähler manifold, ⋆ preserves (p,q) type up to conjugation

### Implementation Strategy

We define a `HodgeStarData` structure that bundles:
1. The Hodge star map ⋆ : Ω^k → Ω^(2n-k)
2. All required properties (linearity, involution)
3. The fundamental relation to inner products

**References**:
- [Warner, "Foundations of Differentiable Manifolds", GTM 94, §6.1]
- [Voisin, "Hodge Theory and Complex Algebraic Geometry I", §5.1]
- [Wells, "Differential Analysis on Complex Manifolds", Ch. IV]
-/

/-- **Sign factor for Hodge star involution**.
    On a 2n-dimensional manifold, ⋆⋆α = (-1)^{k(2n-k)} α for a k-form α. -/
def hodgeStarSign (dim k : ℕ) : ℤ := (-1 : ℤ) ^ (k * (dim - k))

/-- **Hodge Star Data** (Agent 3).

    Bundles the Hodge star operator with its key properties.
    The Hodge star ⋆ : Ω^k → Ω^(2n-k) is characterized by:
    - α ∧ ⋆β = ⟨α, β⟩_x · vol_X (defining relation)
    - ⋆⋆α = (-1)^{k(2n-k)} α (involution)
    - Linearity: ⋆(α + β) = ⋆α + ⋆β, ⋆(cα) = c·⋆α -/
structure HodgeStarData (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] where
  /-- The Hodge star operator maps k-forms to (2n-k)-forms. -/
  star : SmoothForm n X k → SmoothForm n X (2 * n - k)
  /-- Additivity: ⋆(α + β) = ⋆α + ⋆β -/
  star_add : ∀ (α β : SmoothForm n X k), star (α + β) = star α + star β
  /-- ℂ-linearity: ⋆(c • α) = c • ⋆α -/
  star_smul : ∀ (c : ℂ) (α : SmoothForm n X k), star (c • α) = c • star α
  /-- Zero: ⋆0 = 0 -/
  star_zero : star 0 = 0
  /-- Negation: ⋆(-α) = -(⋆α) -/
  star_neg : ∀ (α : SmoothForm n X k), star (-α) = -(star α)

/-- **Hodge Star Data from Fiber-level Construction**.

    Uses the fiber-level Hodge star `fiberHodgeStar_construct` to define the
    pointwise Hodge star on forms.

    **Implementation**: At each point x, applies the fiber Hodge star to α(x).

    **Status**: Uses the fiber-level construction based on real coordinate basis
    decomposition. -/
noncomputable def HodgeStarData.fromFiber (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] : HodgeStarData n X k where
  star := fun α => {
    as_alternating := fun x => fiberHodgeStar_construct n k (α.as_alternating x)
    is_smooth := by
      -- `fiberHodgeStar_construct` is (by definition) a continuous linear map on fibers, hence smooth;
      -- composing with a smooth section remains smooth.
      -- IMPORTANT: our global smoothness is over `ℝ` (see `IsSmoothAlternating`), so we must use the
      -- `ℝ`-linear restriction of the fiber map to get a `ContMDiff` statement with target
      -- `𝓘(ℝ, FiberAlt n k)`.
      simpa [fiberHodgeStar_construct] using
        ((fiberHodgeStarCLM n k).restrictScalars ℝ).contMDiff.comp α.is_smooth
  }
  star_add := fun α β => by
    ext x v
    simp [SmoothForm.add_apply, fiberHodgeStar_add]
  star_smul := fun c α => by
    ext x v
    simp only [SmoothForm.smul_apply]
    -- Use the fiber-level smul lemma
    simpa using congrArg (fun f => f v) (fiberHodgeStar_smul n k c (α.as_alternating x))
  star_zero := by
    ext x v
    simp only [SmoothForm.zero_apply]
    simp [fiberHodgeStar_construct]
  star_neg := fun α => by
    ext x v
    simp only [SmoothForm.neg_apply, ContinuousAlternatingMap.neg_apply]
    -- Use ℂ-linearity of the fiber-level star at scalar `-1`.
    have h := fiberHodgeStar_smul n k (-1 : ℂ) (α.as_alternating x)
    have hx : (-1 : ℂ) • α.as_alternating x = -α.as_alternating x := by
      exact neg_one_smul ℂ (α.as_alternating x)
    have hy :
        (-1 : ℂ) • fiberHodgeStar_construct n k (α.as_alternating x) =
          -fiberHodgeStar_construct n k (α.as_alternating x) := by
      exact neg_one_smul ℂ (fiberHodgeStar_construct n k (α.as_alternating x))
    have h' :
        fiberHodgeStar_construct n k (-α.as_alternating x) =
          -fiberHodgeStar_construct n k (α.as_alternating x) := by
      simpa [hx, hy] using h
    simpa using congrArg (fun f => f v) h'

/-! ### Hodge Star Operator Definition -/

/-- **Hodge star operator** on k-forms.

    Maps a k-form α to a (2n-k)-form ⋆α such that:
    - α ∧ ⋆β = ⟨α, β⟩_x · vol_X
    - ⟨α, β⟩_{L²} = ∫_X α ∧ ⋆β

    Currently uses trivial data (returns 0) until real metric infrastructure is available.

    **Mathematical Definition**: For a Kähler manifold with metric g and volume form vol,
    the Hodge star is uniquely determined by: α ∧ ⋆β = g(α, β) · vol

    **Implementation**: Uses `HodgeStarData.fromFiber` which applies the fiber-level
    Hodge star `fiberHodgeStar_construct` at each point. Once the fiber-level Hodge star
    is upgraded to use real basis decomposition, this will return non-trivial values.

    **Reference**: [Warner, GTM 94, §6.1], [Voisin, "Hodge Theory I", §5.1] -/
noncomputable def hodgeStar {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) : SmoothForm n X (2 * n - k) :=
  (HodgeStarData.fromFiber n X k).star α

/-- Notation for Hodge star operator. -/
notation:max "⋆" α:max => hodgeStar α

/-! ### Hodge Star Basic Properties -/

/-- Hodge star is additive. -/
theorem hodgeStar_add {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α β : SmoothForm n X k) :
    ⋆(α + β) = ⋆α + ⋆β :=
  (HodgeStarData.fromFiber n X k).star_add α β

/-- Hodge star respects scalar multiplication. -/
theorem hodgeStar_smul {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (c : ℂ) (α : SmoothForm n X k) :
    ⋆(c • α) = c • (⋆α) :=
  (HodgeStarData.fromFiber n X k).star_smul c α

/-- Hodge star respects real scalar multiplication (by coercion to ℂ). -/
theorem hodgeStar_smul_real {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (r : ℝ) (α : SmoothForm n X k) :
    ⋆(r • α) = r • (⋆α) := by
  -- `r • α` is defined via the ℂ-action with coercion.
  simpa [SmoothForm.smul_real_apply] using (hodgeStar_smul (n := n) (X := X) (k := k) (c := (r : ℂ)) α)

/-- Hodge star of zero is zero. -/
theorem hodgeStar_zero {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} : ⋆(0 : SmoothForm n X k) = 0 :=
  (HodgeStarData.fromFiber n X k).star_zero

/-- Hodge star respects negation. -/
theorem hodgeStar_neg {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) :
    ⋆(-α) = -(⋆α) :=
  (HodgeStarData.fromFiber n X k).star_neg α

/-- Hodge star respects subtraction. -/
theorem hodgeStar_sub {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α β : SmoothForm n X k) :
    ⋆(α - β) = ⋆α - ⋆β := by
  rw [sub_eq_add_neg, hodgeStar_add, hodgeStar_neg, ← sub_eq_add_neg]

theorem hodgeStar_eq_zero_of_eq_zero_on {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) {U : Set X} (hU : IsOpen U)
    (hzero : ∀ x ∈ U, α.as_alternating x = 0) :
    ∀ x ∈ U, (⋆α).as_alternating x = 0 := by
  intro x hx
  have hzero' : α.as_alternating x = 0 := hzero x hx
  simp [hodgeStar, HodgeStarData.fromFiber, hzero']

private lemma hodgeStar_eventuallyEq_zero_of_eventuallyEq_zero {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) {x : X}
    (hzero : α.as_alternating =ᶠ[nhds x] 0) :
    (⋆α).as_alternating =ᶠ[nhds x] 0 := by
  rcases (Filter.eventuallyEq_iff_exists_mem).1 hzero with ⟨s, hs, hEq⟩
  rcases mem_nhds_iff.mp hs with ⟨U, hUsub, hUopen, hxU⟩
  have hEqU : Set.EqOn α.as_alternating (fun _ : X => (0 : FiberAlt n k)) U := by
    intro y hy
    exact hEq (hUsub hy)
  have hzeroU :
      ∀ y ∈ U, (⋆α).as_alternating y = 0 :=
    hodgeStar_eq_zero_of_eq_zero_on (α := α) hUopen hEqU
  exact Filter.eventuallyEq_of_mem (hUopen.mem_nhds hxU) hzeroU

theorem hodgeStar_tsupport_subset {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) :
    tsupport (⋆α).as_alternating ⊆ tsupport α.as_alternating := by
  intro x hx
  by_contra hx'
  have hzero : α.as_alternating =ᶠ[nhds x] 0 :=
    (notMem_tsupport_iff_eventuallyEq).1 hx'
  have hzero' :
      (⋆α).as_alternating =ᶠ[nhds x] 0 :=
    hodgeStar_eventuallyEq_zero_of_eventuallyEq_zero (α := α) hzero
  have hxnot : x ∉ tsupport (⋆α).as_alternating :=
    (notMem_tsupport_iff_eventuallyEq).2 hzero'
  exact hxnot hx

theorem hodgeStar_hasCompactSupport {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) :
    HasCompactSupport α.as_alternating →
      HasCompactSupport (⋆α).as_alternating := by
  intro hcomp
  have hcompact : IsCompact (tsupport α.as_alternating) := by
    simpa [HasCompactSupport] using hcomp
  have hcompact' : IsCompact (tsupport (⋆α).as_alternating) :=
    IsCompact.of_isClosed_subset hcompact (isClosed_tsupport _)
      (hodgeStar_tsupport_subset (α := α))
  simpa [HasCompactSupport] using hcompact'

/-! ### Hodge Star Involution (Infrastructure)

**Note**: The involution property ⋆⋆α = (-1)^{k(2n-k)} α requires a real Hodge star
operator. The trivial ⋆ = 0 cannot satisfy this (since 0 ≠ sign • α in general).
The infrastructure below is provided for when Agent 5 implements the real Hodge star. -/

/-- **Sign factor for Hodge star involution**.
    On a 2n-dimensional manifold, ⋆⋆α = (-1)^{k(2n-k)} α for a k-form α. -/
def hodgeStarSignℂ (dim k : ℕ) : ℂ := (hodgeStarSign dim k : ℤ)

/-
**Hodge star involution property** (middle dimension, fiber level):

On a 2n-dimensional manifold, for k = n (middle dimension), the fiber Hodge star satisfies:
  ⋆(⋆α) = α (up to type cast for 2n - (2n - n) = n)

**Implementation Note**: For k = n, the fiber-level Hodge star returns the form itself,
so applying it twice returns the original form.

The full sign factor (-1)^{k(2n-k)} is not yet implemented for general k.

**Technical Note**: Proving this requires handling dependent type casts, which is
deferred to future work. The key insight is that `2 * n - n = n` and `2 * n - (2 * n - n) = n`,
so after the casts, we get α back.

(Formal theorem statement deferred due to dependent type complexity)
-/

/-! ### Codifferential (Adjoint of Exterior Derivative) -/

/-- **Codifferential** δ = (-1)^{nk+n+1} ⋆ d ⋆ (sign factor).

    The codifferential δ is the formal L2-adjoint of the exterior derivative d:
    ⟨dα, β⟩ = ⟨α, δβ⟩

    On k-forms: δ : Ω^k → Ω^{k-1} with δ = (-1)^{nk+n+1} ⋆ d ⋆

    **Note**: This is just the sign factor definition. The full codifferential
    requires careful handling of degrees and is infrastructure for future work. -/
def codifferentialSign (dim k : ℕ) : ℤ := (-1 : ℤ) ^ (dim * k + dim + 1)

end
