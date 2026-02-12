import Hodge.Analytic.Integration.VolumeForm
import Hodge.Analytic.Integration.HausdorffMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-!
# Top-Form Integration on Compact Kähler Manifolds

This file defines integration of top-forms (2n-forms) on compact Kähler manifolds.

## Main Definitions

* `topFormIntegral_real`: Integration of a top-form over X, returning a real number
* `topFormIntegral_complex`: Complex-valued version
* `topFormIntegral_linearMap`: The integration map as a continuous linear functional

## Mathematical Background

On a compact complex n-dimensional Kähler manifold X:
- Top forms have degree 2n (the real dimension)
- For a top-form η, the integral ∫_X η is well-defined
- Integration is linear: ∫_X (aη₁ + η₂) = a∫_X η₁ + ∫_X η₂
- Integration is bounded: |∫_X η| ≤ vol(X) · ‖η‖_∞

## References

* [Griffiths-Harris, "Principles of Algebraic Geometry", Chapter 0]
* [Voisin, "Hodge Theory and Complex Algebraic Geometry I", Chapter 5]
* [Warner, "Foundations of Differentiable Manifolds and Lie Groups", Chapter 4]

## Implementation Status

✅ **COMPLETE** - All definitions implemented, no `sorry` statements on proof track.

The integration infrastructure uses placeholder definitions for now. Any deep
analytic facts that are **off the proof track** are kept as documentation-only
comments (no semantic stub theorems).

-/

noncomputable section

open Classical Hodge MeasureTheory

set_option autoImplicit false

universe u

variable {n : ℕ} {X : Type u}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X]

variable [K : KahlerManifold n X]
-- Explicit integration data (legacy SubmanifoldIntegration refactored to data object).

private lemma castForm_add {k k' : ℕ} (h : k = k') (ω₁ ω₂ : SmoothForm n X k) :
    castForm h (ω₁ + ω₂) = castForm h ω₁ + castForm h ω₂ := by
  subst h
  simp

private lemma castForm_smul {k k' : ℕ} (h : k = k') (c : ℝ) (ω : SmoothForm n X k) :
    castForm h (c • ω) = c • castForm h ω := by
  subst h
  simp

private lemma smoothWedge_smul_left_real {k l : ℕ} (r : ℝ)
    (ω : SmoothForm n X k) (η : SmoothForm n X l) :
    (r • ω) ⋏ η = r • (ω ⋏ η) := by
  ext x v
  simp [SmoothForm.wedge_apply, SmoothForm.smul_real_apply,
    ContinuousAlternatingMap.wedgeℂ_smul_left]

private lemma smoothWedge_smul_right_real {k l : ℕ} (r : ℝ)
    (ω : SmoothForm n X k) (η : SmoothForm n X l) :
    ω ⋏ (r • η) = r • (ω ⋏ η) := by
  ext x v
  simp [SmoothForm.wedge_apply, SmoothForm.smul_real_apply,
    ContinuousAlternatingMap.wedgeℂ_smul_right]

/-! ## Real-Valued Integration of Top Forms -/

/-- **Integration of a top-form over X** (Real-valued).

    For a (2n)-form η on a compact complex n-dimensional Kähler manifold X:
    `∫_X η = ∫_X ⟨η, vol^{-1}⟩ dμ`

    where μ is the Kähler measure and vol^{-1} is the dual volume element.

    **Mathematical Properties**:
    - Linear: ∫_X (aη₁ + η₂) = a∫_X η₁ + ∫_X η₂
    - Bounded: |∫_X η| ≤ vol(X) · ‖η‖_∞
    - For η = f · vol: ∫_X η = ∫_X f dμ

    **Implementation Status** (Round 10): Nontrivial implementation using
    `integrateDegree2p` over the whole manifold `Set.univ`.

    Reference: [Griffiths-Harris, "Principles of Algebraic Geometry", §0.6]. -/
noncomputable def topFormIntegral_real' (data : SubmanifoldIntegrationData n X)
    (η : SmoothForm n X (2 * n)) : ℝ :=
  integrateDegree2p (n := n) (X := X) (k := 2 * n) Set.univ η data

/-- **Integration is linear**.

    **Proof Status**: Proved via `integrateDegree2p_linear`.

    Reference: [Warner, "Foundations of Differentiable Manifolds", §4.8]. -/
theorem topFormIntegral_real'_linear (data : SubmanifoldIntegrationData n X)
    (c : ℝ) (η₁ η₂ : SmoothForm n X (2 * n)) :
    topFormIntegral_real' (n := n) (X := X) data (c • η₁ + η₂) =
      c * topFormIntegral_real' (n := n) (X := X) data η₁ +
        topFormIntegral_real' (n := n) (X := X) data η₂ := by
  unfold topFormIntegral_real'
  exact integrateDegree2p_linear (n := n) (X := X) (k := 2 * n) Set.univ data c η₁ η₂

/-- **Integration of zero form is zero**.

    **Proof Status**: Proved via `integrateDegree2p_linear`.

    Reference: [Warner, "Foundations of Differentiable Manifolds", §4.8]. -/
theorem topFormIntegral_real'_zero (data : SubmanifoldIntegrationData n X) :
    topFormIntegral_real' (n := n) (X := X) data (0 : SmoothForm n X (2 * n)) = 0 := by
  unfold topFormIntegral_real'
  -- Use the fact that integrateDegree2p is linear: ∫(0•0 + 0) = 0*∫0 + ∫0
  have h :=
    integrateDegree2p_linear (n := n) (X := X) (k := 2 * n) Set.univ data 0 0 0
  simp only [zero_smul, zero_add, MulZeroClass.zero_mul] at h
  -- Now h : integrateDegree2p ... 0 = integrateDegree2p ... 0, which is reflexive
  -- We need to show integrateDegree2p ... 0 = 0 directly
  -- Use: 2*∫0 = ∫(1•0 + 0) = 1*∫0 + ∫0 = 2*∫0, so we need another approach
  -- Better: ∫(0•η + 0) = 0*∫η + ∫0 for any η, which gives ∫0 = ∫0
  -- Actually: ∫(0 + 0) = ∫0 + ∫0, so ∫0 = 2*∫0, hence ∫0 = 0
  have h2 :=
    integrateDegree2p_linear (n := n) (X := X) (k := 2 * n) Set.univ data 1 0 0
  simp only [one_smul, add_zero, _root_.one_mul] at h2
  linarith

/-- **Integration is additive**.

    **Proof Status**: Proved via linearity with c=1.

    Reference: [Warner, "Foundations of Differentiable Manifolds", §4.8]. -/
theorem topFormIntegral_real'_add (data : SubmanifoldIntegrationData n X)
    (η₁ η₂ : SmoothForm n X (2 * n)) :
    topFormIntegral_real' (n := n) (X := X) data (η₁ + η₂) =
      topFormIntegral_real' (n := n) (X := X) data η₁ +
        topFormIntegral_real' (n := n) (X := X) data η₂ := by
  have h := topFormIntegral_real'_linear (n := n) (X := X) data 1 η₁ η₂
  simp only [one_smul, _root_.one_mul] at h
  exact h

/-- **Integration respects scalar multiplication**.

    **Proof Status**: Proved via linearity with η₂=0.

    Reference: [Warner, "Foundations of Differentiable Manifolds", §4.8]. -/
theorem topFormIntegral_real'_smul (data : SubmanifoldIntegrationData n X)
    (c : ℝ) (η : SmoothForm n X (2 * n)) :
    topFormIntegral_real' (n := n) (X := X) data (c • η) =
      c * topFormIntegral_real' (n := n) (X := X) data η := by
  have h := topFormIntegral_real'_linear (n := n) (X := X) data c η 0
  simp only [add_zero] at h
  rw [topFormIntegral_real'_zero (n := n) (X := X) data] at h
  simp only [add_zero] at h
  exact h

/-- **Integration is bounded by volume times comass**.

    |∫_X η| ≤ vol(X) · comass(η)

    This is the fundamental estimate for integration.

    **Proof Status**: Proved via `integrateDegree2p_bound`.

    Reference: [Federer, "Geometric Measure Theory", §4.1.7]. -/
theorem topFormIntegral_real'_bound (data : SubmanifoldIntegrationData n X)
    (η : SmoothForm n X (2 * n)) :
    |topFormIntegral_real' (n := n) (X := X) data η| ≤
      (hausdorffMeasure2p (n := n) (X := X) n data Set.univ).toReal * ‖η‖ := by
  unfold topFormIntegral_real'
  have h := integrateDegree2p_bound (n := n) (X := X) (k := 2 * n) Set.univ η data
  have hdim : (2 * n) / 2 = n := by
    simpa [Nat.mul_comm] using (Nat.mul_div_right n 2)
  rw [hdim] at h
  exact h

/-! ## Complex-Valued Integration -/

/-- **Complex-valued integration of a top-form**.

    This extends `topFormIntegral_real'` to complex scalars.

    **Implementation Status** (Round 10): Nontrivial implementation via
    `Complex.ofReal ∘ topFormIntegral_real'`.

    Reference: [Griffiths-Harris, "Principles of Algebraic Geometry", §0.6]. -/
noncomputable def topFormIntegral_complex (data : SubmanifoldIntegrationData n X)
    (η : SmoothForm n X (2 * n)) : ℂ :=
  Complex.ofReal (topFormIntegral_real' (n := n) (X := X) data η)

/-- **Complex integration is ℂ-linear** (in restricted sense).

    **Note**: Full ℂ-linearity would require `topFormIntegral_complex (c • η) = c * topFormIntegral_complex η`.
    Since we're building on real integration, we have ℝ-linearity lifted to ℂ.

    **Proof Status**: Proved via real linearity.

    Reference: [Griffiths-Harris, "Principles of Algebraic Geometry", §0.6]. -/
theorem topFormIntegral_complex_add (data : SubmanifoldIntegrationData n X)
    (η₁ η₂ : SmoothForm n X (2 * n)) :
    topFormIntegral_complex (n := n) (X := X) data (η₁ + η₂) =
      topFormIntegral_complex (n := n) (X := X) data η₁ +
        topFormIntegral_complex (n := n) (X := X) data η₂ := by
  unfold topFormIntegral_complex
  rw [topFormIntegral_real'_add (n := n) (X := X) data]
  push_cast
  ring

theorem topFormIntegral_complex_smul_real (data : SubmanifoldIntegrationData n X)
    (c : ℝ) (η : SmoothForm n X (2 * n)) :
    topFormIntegral_complex (n := n) (X := X) data (c • η) =
      c * topFormIntegral_complex (n := n) (X := X) data η := by
  unfold topFormIntegral_complex
  rw [topFormIntegral_real'_smul (n := n) (X := X) data]
  push_cast
  ring

/-! ## Integration as a Linear Map -/

/-- **Integration as a continuous ℝ-linear map**.

    This packages the integration functional as a LinearMap, which is useful
    for functional-analytic arguments.

    **Implementation Status**: Complete using topFormIntegral_real'.

    Reference: [Warner, "Foundations of Differentiable Manifolds", §4.8]. -/
noncomputable def topFormIntegral_linearMap (data : SubmanifoldIntegrationData n X) :
    SmoothForm n X (2 * n) →ₗ[ℝ] ℝ where
  toFun := topFormIntegral_real' (n := n) (X := X) data
  map_add' := topFormIntegral_real'_add (n := n) (X := X) data
  map_smul' := fun r η => by
    simp only [RingHom.id_apply]
    exact topFormIntegral_real'_smul (n := n) (X := X) data r η

/-- **Integration is continuous**.

    In the comass topology on forms, integration is a continuous linear functional.
    Since SmoothForm has the discrete topology, this is trivially true.

    **Proof Status**: Proved (trivial since SmoothForm has discrete topology).

    Reference: [Warner, "Foundations of Differentiable Manifolds", §4.8]. -/
theorem topFormIntegral_continuous (data : SubmanifoldIntegrationData n X) :
    Continuous (topFormIntegral_real' (n := n) (X := X) data) :=
by
  -- `topFormIntegral_real'` is ℝ-linear and bounded by `topFormIntegral_real'_bound`,
  -- hence continuous in the comass seminorm topology on forms.
  classical
  let f : SmoothForm n X (2 * n) →ₗ[ℝ] ℝ :=
    topFormIntegral_linearMap (n := n) (X := X) data
  have hbound : ∃ C, ∀ η, ‖f η‖ ≤ C * ‖η‖ := by
    refine ⟨(hausdorffMeasure2p (n := n) (X := X) n data Set.univ).toReal, ?_⟩
    intro η
    -- `‖f η‖ = |f η|` for ℝ, and `f η = topFormIntegral_real' η` by definition.
    simpa [f, topFormIntegral_linearMap, Real.norm_eq_abs] using
      (topFormIntegral_real'_bound (n := n) (X := X) data η)
  -- Build the associated continuous linear map, then extract continuity of the underlying function.
  simpa [f, topFormIntegral_linearMap] using (f.mkContinuousOfExistsBound hbound).continuous

/-! ## Integration of Volume Form -/

/-! **Integration of the volume form gives the total volume** (documentation-only).

    ∫_X vol = vol(X)

    This will be formalized once measure-theory integration is connected.

    Reference: [Griffiths-Harris, "Principles of Algebraic Geometry", §0.2]. -/

/-! **Volume integral is positive** (documentation-only).

    ∫_X vol > 0 for nonempty compact Kähler manifolds.

    This will be formalized once measure-theory integration is connected.

    Reference: [Griffiths-Harris, "Principles of Algebraic Geometry", §0.2]. -/

/-! ## Stokes' Theorem for Top Forms -/

/-! **Stokes' Theorem for closed manifolds**: ∫_X dη = 0 (documentation-only).

    On a compact manifold without boundary, the integral of an exact form vanishes.

    This will be formalized once Stokes' theorem is on-track.

    Reference: [Warner, "Foundations of Differentiable Manifolds", §4.9]. -/

/-! ## Pairing of Complementary-Degree Forms -/

/-- **Intersection pairing** (Poincaré duality).

    For α ∈ Ω^{2p}(X) and β ∈ Ω^{2(n-p)}(X), define:
    `⟨α, β⟩ = ∫_X α ∧ β`

    This defines the intersection pairing on cohomology.

    **Implementation Status**: Defined using topFormIntegral_real'.
    Sprint 2 will verify this matches the pairing in Microstructure.lean.

    Reference: [Griffiths-Harris, "Principles of Algebraic Geometry", §0.6]. -/
noncomputable def intersectionPairing {p : ℕ} (_hp : p ≤ n)
    (data : SubmanifoldIntegrationData n X)
    (α : SmoothForm n X (2 * p)) (β : SmoothForm n X (2 * (n - p))) : ℝ :=
  -- α ∧ β has degree 2p + 2(n-p) = 2n
  have hdeg : 2 * p + 2 * (n - p) = 2 * n := by omega
  topFormIntegral_real' (n := n) (X := X) data (castForm hdeg (α ⋏ β))

theorem intersectionPairing_add_left {p : ℕ} (hp : p ≤ n)
    (data : SubmanifoldIntegrationData n X)
    (α₁ α₂ : SmoothForm n X (2 * p)) (β : SmoothForm n X (2 * (n - p))) :
    intersectionPairing (n := n) (X := X) hp data (α₁ + α₂) β =
      intersectionPairing (n := n) (X := X) hp data α₁ β +
        intersectionPairing (n := n) (X := X) hp data α₂ β := by
  classical
  unfold intersectionPairing
  have hdeg : 2 * p + 2 * (n - p) = 2 * n := by omega
  have hcast :
      castForm hdeg ((α₁ + α₂) ⋏ β) =
        castForm hdeg (α₁ ⋏ β) + castForm hdeg (α₂ ⋏ β) := by
    simpa [smoothWedge_add_left] using
      (castForm_add (h := hdeg) (ω₁ := α₁ ⋏ β) (ω₂ := α₂ ⋏ β))
  simpa [hcast] using
    (topFormIntegral_real'_add (n := n) (X := X) data
      (η₁ := castForm hdeg (α₁ ⋏ β)) (η₂ := castForm hdeg (α₂ ⋏ β)))

theorem intersectionPairing_add_right {p : ℕ} (hp : p ≤ n)
    (data : SubmanifoldIntegrationData n X)
    (α : SmoothForm n X (2 * p)) (β₁ β₂ : SmoothForm n X (2 * (n - p))) :
    intersectionPairing (n := n) (X := X) hp data α (β₁ + β₂) =
      intersectionPairing (n := n) (X := X) hp data α β₁ +
        intersectionPairing (n := n) (X := X) hp data α β₂ := by
  classical
  unfold intersectionPairing
  have hdeg : 2 * p + 2 * (n - p) = 2 * n := by omega
  have hcast :
      castForm hdeg (α ⋏ (β₁ + β₂)) =
        castForm hdeg (α ⋏ β₁) + castForm hdeg (α ⋏ β₂) := by
    simpa [smoothWedge_add_right] using
      (castForm_add (h := hdeg) (ω₁ := α ⋏ β₁) (ω₂ := α ⋏ β₂))
  simpa [hcast] using
    (topFormIntegral_real'_add (n := n) (X := X) data
      (η₁ := castForm hdeg (α ⋏ β₁)) (η₂ := castForm hdeg (α ⋏ β₂)))

theorem intersectionPairing_smul_left {p : ℕ} (hp : p ≤ n)
    (data : SubmanifoldIntegrationData n X) (r : ℝ)
    (α : SmoothForm n X (2 * p)) (β : SmoothForm n X (2 * (n - p))) :
    intersectionPairing (n := n) (X := X) hp data (r • α) β =
      r * intersectionPairing (n := n) (X := X) hp data α β := by
  classical
  unfold intersectionPairing
  have hdeg : 2 * p + 2 * (n - p) = 2 * n := by omega
  have hcast :
      castForm hdeg ((r • α) ⋏ β) = r • castForm hdeg (α ⋏ β) := by
    simpa [smoothWedge_smul_left_real] using
      (castForm_smul (h := hdeg) (c := r) (ω := α ⋏ β))
  simpa [hcast] using
    (topFormIntegral_real'_smul (n := n) (X := X) data (c := r)
      (η := castForm hdeg (α ⋏ β)))

theorem intersectionPairing_smul_right {p : ℕ} (hp : p ≤ n)
    (data : SubmanifoldIntegrationData n X) (r : ℝ)
    (α : SmoothForm n X (2 * p)) (β : SmoothForm n X (2 * (n - p))) :
    intersectionPairing (n := n) (X := X) hp data α (r • β) =
      r * intersectionPairing (n := n) (X := X) hp data α β := by
  classical
  unfold intersectionPairing
  have hdeg : 2 * p + 2 * (n - p) = 2 * n := by omega
  have hcast :
      castForm hdeg (α ⋏ (r • β)) = r • castForm hdeg (α ⋏ β) := by
    simpa [smoothWedge_smul_right_real] using
      (castForm_smul (h := hdeg) (c := r) (ω := α ⋏ β))
  simpa [hcast] using
    (topFormIntegral_real'_smul (n := n) (X := X) data (c := r)
      (η := castForm hdeg (α ⋏ β)))

/-! ## L2 Inner Product via Hodge Star -/

/-- **L2 inner product via Hodge star**.

    For k-forms α, β, define:
    `⟪α, β⟫ = ∫_X α ∧ ⋆β`.
    This matches the usual L2 pairing once the metric/volume-form normalization is aligned. -/
noncomputable def L2Inner_wedge {k : ℕ} (hk : k ≤ 2 * n)
    (data : SubmanifoldIntegrationData n X)
    (α β : SmoothForm n X k) : ℝ :=
  have hdeg : k + (2 * n - k) = 2 * n := by
    exact Nat.add_sub_of_le hk
  topFormIntegral_real' (n := n) (X := X) data (castForm hdeg (α ⋏ ⋆β))

theorem L2Inner_wedge_add_left {k : ℕ} (hk : k ≤ 2 * n)
    (data : SubmanifoldIntegrationData n X)
    (α₁ α₂ β : SmoothForm n X k) :
    L2Inner_wedge (n := n) (X := X) (k := k) hk data (α₁ + α₂) β =
      L2Inner_wedge (n := n) (X := X) (k := k) hk data α₁ β +
        L2Inner_wedge (n := n) (X := X) (k := k) hk data α₂ β := by
  classical
  unfold L2Inner_wedge
  have hdeg : k + (2 * n - k) = 2 * n := by
    exact Nat.add_sub_of_le hk
  have hcast :
      castForm hdeg ((α₁ + α₂) ⋏ ⋆β) =
        castForm hdeg (α₁ ⋏ ⋆β) + castForm hdeg (α₂ ⋏ ⋆β) := by
    simpa [smoothWedge_add_left] using
      (castForm_add (h := hdeg) (ω₁ := α₁ ⋏ ⋆β) (ω₂ := α₂ ⋏ ⋆β))
  simpa [hcast] using
    (topFormIntegral_real'_add (n := n) (X := X) data
      (η₁ := castForm hdeg (α₁ ⋏ ⋆β)) (η₂ := castForm hdeg (α₂ ⋏ ⋆β)))

theorem L2Inner_wedge_add_right {k : ℕ} (hk : k ≤ 2 * n)
    (data : SubmanifoldIntegrationData n X)
    (α : SmoothForm n X k) (β₁ β₂ : SmoothForm n X k) :
    L2Inner_wedge (n := n) (X := X) (k := k) hk data α (β₁ + β₂) =
      L2Inner_wedge (n := n) (X := X) (k := k) hk data α β₁ +
        L2Inner_wedge (n := n) (X := X) (k := k) hk data α β₂ := by
  classical
  unfold L2Inner_wedge
  have hdeg : k + (2 * n - k) = 2 * n := by
    exact Nat.add_sub_of_le hk
  have hcast :
      castForm hdeg (α ⋏ ⋆(β₁ + β₂)) =
        castForm hdeg (α ⋏ ⋆β₁) + castForm hdeg (α ⋏ ⋆β₂) := by
    simpa [hodgeStar_add, smoothWedge_add_right] using
      (castForm_add (h := hdeg) (ω₁ := α ⋏ ⋆β₁) (ω₂ := α ⋏ ⋆β₂))
  simpa [hcast] using
    (topFormIntegral_real'_add (n := n) (X := X) data
      (η₁ := castForm hdeg (α ⋏ ⋆β₁)) (η₂ := castForm hdeg (α ⋏ ⋆β₂)))

theorem L2Inner_wedge_smul_left {k : ℕ} (hk : k ≤ 2 * n)
    (data : SubmanifoldIntegrationData n X)
    (r : ℝ) (α : SmoothForm n X k)
    (β : SmoothForm n X k) :
    L2Inner_wedge (n := n) (X := X) (k := k) hk data (r • α) β =
      r * L2Inner_wedge (n := n) (X := X) (k := k) hk data α β := by
  classical
  unfold L2Inner_wedge
  have hdeg : k + (2 * n - k) = 2 * n := by
    exact Nat.add_sub_of_le hk
  have hcast :
      castForm hdeg ((r • α) ⋏ ⋆β) = r • castForm hdeg (α ⋏ ⋆β) := by
    simpa [smoothWedge_smul_left_real] using
      (castForm_smul (h := hdeg) (c := r) (ω := α ⋏ ⋆β))
  simpa [hcast] using
    (topFormIntegral_real'_smul (n := n) (X := X) data (c := r)
      (η := castForm hdeg (α ⋏ ⋆β)))

theorem L2Inner_wedge_smul_right {k : ℕ} (hk : k ≤ 2 * n)
    (data : SubmanifoldIntegrationData n X)
    (r : ℝ) (α : SmoothForm n X k)
    (β : SmoothForm n X k) :
    L2Inner_wedge (n := n) (X := X) (k := k) hk data α (r • β) =
      r * L2Inner_wedge (n := n) (X := X) (k := k) hk data α β := by
  classical
  unfold L2Inner_wedge
  have hdeg : k + (2 * n - k) = 2 * n := by
    exact Nat.add_sub_of_le hk
  have hcast :
      castForm hdeg (α ⋏ ⋆(r • β)) = r • castForm hdeg (α ⋏ ⋆β) := by
    simpa [hodgeStar_smul_real, smoothWedge_smul_right_real] using
      (castForm_smul (h := hdeg) (c := r) (ω := α ⋏ ⋆β))
  simpa [hcast] using
    (topFormIntegral_real'_smul (n := n) (X := X) data (c := r)
      (η := castForm hdeg (α ⋏ ⋆β)))

/-! **Intersection pairing is bilinear in the first argument** (documentation-only).

    Full bilinearity requires wedge product linearity combined with integration linearity.

    Reference: [Griffiths-Harris, "Principles of Algebraic Geometry", §0.6]. -/

/-! **Intersection pairing is bilinear in the second argument** (documentation-only).

    Full bilinearity requires wedge product linearity combined with integration linearity.

    Reference: [Griffiths-Harris, "Principles of Algebraic Geometry", §0.6]. -/

/-! **Intersection pairing descends to cohomology** (Stokes; documentation-only).

    If α is closed and β is exact, then ⟨α, β⟩ = 0.

    Full proof requires Stokes: if β = dγ and dα = 0, then
    ∫_X α ∧ dγ = ±∫_X d(α ∧ γ) = 0.

    Reference: [Griffiths-Harris, "Principles of Algebraic Geometry", §0.6]. -/

end
