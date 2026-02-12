/-
Copyright (c) 2026 Hodge Formalization Project. All rights reserved.
Released under Apache 2.0 license.
Authors: Agent 2 (Integration Theory), Agent 3 (Round 8 Plumbing)
-/
import Hodge.Analytic.Forms
import Hodge.Analytic.Norms
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Hausdorff Measure and Integration on Submanifolds

This file provides infrastructure for integrating differential forms over
submanifolds using Hausdorff measure.
-/

noncomputable section

open Classical MeasureTheory Hodge
open scoped Manifold ENNReal

set_option autoImplicit false

universe u

variable {n : ℕ} {X : Type u}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X]

/-! ## Submanifold Integration Data (Explicit, No Typeclass) -/

/-- **SubmanifoldIntegrationData**: explicit data packaging the deep GMT integration infrastructure.
    This refactors the legacy typeclass into a concrete object to avoid hidden assumptions. -/
structure SubmanifoldIntegrationData (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [Nonempty X] where
  /-- Hausdorff measure of dimension 2p -/
  measure2p : ℕ → Measure X
  /-- Finiteness of the Hausdorff measure on compact Kähler manifolds. -/
  measure2p_finite : ∀ p, (measure2p p) Set.univ < ∞
  /-- Integration functional: ω ↦ ∫_Z ω -/
  integral : ∀ (p : ℕ), SmoothForm n X (2 * p) → Set X → ℝ
  /-- Linearity -/
  integral_linear : ∀ (p : ℕ) (Z : Set X) (c : ℝ) (ω₁ ω₂ : SmoothForm n X (2 * p)),
    integral p (c • ω₁ + ω₂) Z = c * integral p ω₁ Z + integral p ω₂ Z
  /-- Additivity over disjoint sets -/
  integral_union : ∀ (p : ℕ) (ω : SmoothForm n X (2 * p)) (Z₁ Z₂ : Set X),
    Disjoint Z₁ Z₂ → MeasurableSet Z₁ → MeasurableSet Z₂ →
    integral p ω (Z₁ ∪ Z₂) = integral p ω Z₁ + integral p ω Z₂
  /-- Empty set gives zero -/
  integral_empty : ∀ (p : ℕ) (ω : SmoothForm n X (2 * p)), integral p ω ∅ = 0
  /-- Comass bound -/
  integral_bound : ∀ (p : ℕ) (ω : SmoothForm n X (2 * p)) (Z : Set X),
    |integral p ω Z| ≤ (measure2p p Z).toReal * ‖ω‖
  /-- **Stokes' theorem for this integration theory**: exact forms integrate to zero on closed sets.

  This is the key GMT input behind the data‑first Stokes bounds in `Currents.lean`
  (legacy `StokesTheoremData` is no longer used on the proof track).

  We phrase it in a way that matches the `integrateDegree2p` dispatcher:
  when `k+1` is even and `k+1 = 2*p`, the casted exterior derivative integrates to zero.
  -/
  stokes_integral_zero :
    ∀ {k p : ℕ} (hkp : k + 1 = 2 * p) (ω : SmoothForm n X k) (Z : Set X),
      IsClosed Z → integral p (castForm hkp (smoothExtDeriv ω)) Z = 0

/-- Legacy typeclass wrapper for backward compatibility.

Prefer using explicit `SubmanifoldIntegrationData` instead of this class. -/
class SubmanifoldIntegration (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [Nonempty X] where
  data : SubmanifoldIntegrationData n X

/-- Extract explicit data from the legacy typeclass wrapper. -/
noncomputable def submanifoldIntegrationDataOf
    [SubmanifoldIntegration n X] : SubmanifoldIntegrationData n X :=
  SubmanifoldIntegration.data (n := n) (X := X)

/-! ## Hausdorff Measure on Submanifolds -/

/-- The real dimension of a complex p-dimensional submanifold. -/
def realDimension (p : ℕ) : ℕ := 2 * p

/-- Hausdorff measure of dimension 2p on X. -/
noncomputable def hausdorffMeasure2p (p : ℕ) (data : SubmanifoldIntegrationData n X) : Measure X :=
  data.measure2p p

theorem hausdorffMeasure2p_finite (p : ℕ) (data : SubmanifoldIntegrationData n X) :
    (hausdorffMeasure2p (n := n) (X := X) p data) Set.univ < ∞ :=
  data.measure2p_finite p

/-- **Submanifold integration** (explicit data). -/
noncomputable def submanifoldIntegral {p : ℕ} (data : SubmanifoldIntegrationData n X)
    (ω : SmoothForm n X (2 * p)) (Z : Set X) : ℝ :=
  data.integral p ω Z

/-- Submanifold integration is linear in the form. -/
theorem submanifoldIntegral_linear {p : ℕ} (data : SubmanifoldIntegrationData n X) (Z : Set X)
    (c : ℝ) (ω₁ ω₂ : SmoothForm n X (2 * p)) :
    submanifoldIntegral (n := n) (X := X) (p := p) data (c • ω₁ + ω₂) Z =
      c * submanifoldIntegral (n := n) (X := X) (p := p) data ω₁ Z +
        submanifoldIntegral (n := n) (X := X) (p := p) data ω₂ Z := by
  simp [submanifoldIntegral, data.integral_linear p Z c ω₁ ω₂]

/-- Submanifold integration is additive in the set for disjoint sets. -/
theorem submanifoldIntegral_union {p : ℕ} (data : SubmanifoldIntegrationData n X)
    (ω : SmoothForm n X (2 * p))
    (Z₁ Z₂ : Set X) (hZ : Disjoint Z₁ Z₂) (hZ₁ : MeasurableSet Z₁) (hZ₂ : MeasurableSet Z₂) :
    submanifoldIntegral (n := n) (X := X) (p := p) data ω (Z₁ ∪ Z₂) =
      submanifoldIntegral (n := n) (X := X) (p := p) data ω Z₁ +
        submanifoldIntegral (n := n) (X := X) (p := p) data ω Z₂ := by
  simp [submanifoldIntegral, data.integral_union p ω Z₁ Z₂ hZ hZ₁ hZ₂]

/-- Integration over the empty set is zero. -/
theorem submanifoldIntegral_empty {p : ℕ} (data : SubmanifoldIntegrationData n X)
    (ω : SmoothForm n X (2 * p)) :
    submanifoldIntegral (n := n) (X := X) (p := p) data ω ∅ = 0 := by
  simp [submanifoldIntegral, data.integral_empty p ω]

/-- Submanifold integration is bounded by the form norm. -/
theorem submanifoldIntegral_abs_le {p : ℕ} (data : SubmanifoldIntegrationData n X)
    (ω : SmoothForm n X (2 * p)) (Z : Set X) :
    |submanifoldIntegral (n := n) (X := X) (p := p) data ω Z| ≤
      (hausdorffMeasure2p (n := n) (X := X) p data Z).toReal * ‖ω‖ := by
  simp [submanifoldIntegral, hausdorffMeasure2p, data.integral_bound p ω Z]

/-! ## Integration Currents -/

/-- **Integration current** associated to a submanifold. -/
noncomputable def integrationCurrentValue {p : ℕ} (data : SubmanifoldIntegrationData n X)
    (Z : Set X) (ω : SmoothForm n X (2 * p)) : ℝ :=
  submanifoldIntegral (n := n) (X := X) (p := p) data ω Z

/-- Integration current is linear. -/
theorem integrationCurrentValue_linear {p : ℕ} (data : SubmanifoldIntegrationData n X) (Z : Set X)
    (c : ℝ) (ω₁ ω₂ : SmoothForm n X (2 * p)) :
    integrationCurrentValue (n := n) (X := X) (p := p) data Z (c • ω₁ + ω₂) =
      c * integrationCurrentValue (n := n) (X := X) (p := p) data Z ω₁ +
        integrationCurrentValue (n := n) (X := X) (p := p) data Z ω₂ :=
  submanifoldIntegral_linear (n := n) (X := X) (p := p) data Z c ω₁ ω₂

/-! ## Helper Lemmas for Explicit Submanifold Integration -/

/-- Submanifold integration is additive in the form. -/
theorem submanifoldIntegral_add {p : ℕ} (data : SubmanifoldIntegrationData n X) (Z : Set X)
    (ω₁ ω₂ : SmoothForm n X (2 * p)) :
    submanifoldIntegral (n := n) (X := X) (p := p) data (ω₁ + ω₂) Z =
      submanifoldIntegral (n := n) (X := X) (p := p) data ω₁ Z +
        submanifoldIntegral (n := n) (X := X) (p := p) data ω₂ Z := by
  have h := submanifoldIntegral_linear (n := n) (X := X) (p := p) data Z 1 ω₁ ω₂
  simp only [one_smul, _root_.one_mul] at h
  exact h

/-- Submanifold integration of zero is zero. -/
theorem submanifoldIntegral_zero {p : ℕ} (data : SubmanifoldIntegrationData n X) (Z : Set X) :
    submanifoldIntegral (n := n) (X := X) (p := p) data (0 : SmoothForm n X (2 * p)) Z = 0 := by
  have h := submanifoldIntegral_linear (n := n) (X := X) (p := p) data Z 1
    (0 : SmoothForm n X (2 * p)) 0
  have h' :
      submanifoldIntegral (n := n) (X := X) (p := p) data (0 : SmoothForm n X (2 * p)) Z =
      2 * submanifoldIntegral (n := n) (X := X) (p := p) data (0 : SmoothForm n X (2 * p)) Z := by
    simpa [one_smul, two_mul, add_comm, add_left_comm, add_assoc] using h
  linarith

/-- Submanifold integration commutes with scalar multiplication. -/
theorem submanifoldIntegral_smul {p : ℕ} (data : SubmanifoldIntegrationData n X) (Z : Set X)
    (c : ℝ) (ω : SmoothForm n X (2 * p)) :
    submanifoldIntegral (n := n) (X := X) (p := p) data (c • ω) Z =
      c * submanifoldIntegral (n := n) (X := X) (p := p) data ω Z := by
  have h := submanifoldIntegral_linear (n := n) (X := X) (p := p) data Z c ω 0
  simp only [add_zero] at h
  have hz :
      submanifoldIntegral (n := n) (X := X) (p := p) data (0 : SmoothForm n X (2 * p)) Z = 0 :=
    submanifoldIntegral_zero (n := n) (X := X) data Z
  simp only [hz, add_zero] at h
  exact h

/-- Submanifold integration packaged as a linear map. -/
noncomputable def submanifoldIntegral_asLinearMap {p : ℕ}
    (data : SubmanifoldIntegrationData n X) (Z : Set X) :
    SmoothForm n X (2 * p) →ₗ[ℝ] ℝ where
  toFun := fun ω => submanifoldIntegral (n := n) (X := X) (p := p) data ω Z
  map_add' := fun ω₁ ω₂ => submanifoldIntegral_add (n := n) (X := X) data Z ω₁ ω₂
  map_smul' := fun c ω => by
    simp only [RingHom.id_apply]
    exact submanifoldIntegral_smul (n := n) (X := X) data Z c ω

private lemma castForm_add {k k' : ℕ} (h : k = k') (ω₁ ω₂ : SmoothForm n X k) :
    castForm h (ω₁ + ω₂) = castForm h ω₁ + castForm h ω₂ := by
  subst h
  simp

private lemma castForm_smul {k k' : ℕ} (h : k = k') (c : ℝ) (ω : SmoothForm n X k) :
    castForm h (c • ω) = c • castForm h ω := by
  subst h
  simp

private lemma castForm_norm {k k' : ℕ} (h : k = k') (ω : SmoothForm n X k) :
    ‖castForm h ω‖ = ‖ω‖ := by
  subst h
  simp

/-- **Degree-dispatch integration**. -/
noncomputable def integrateDegree2p (k : ℕ) (Z : Set X) (ω : SmoothForm n X k)
    (data : SubmanifoldIntegrationData n X) : ℝ :=
  if hk : 2 ∣ k then
    let p := k / 2
    have hkp : k = 2 * p := Nat.eq_mul_of_div_eq_right hk rfl
    submanifoldIntegral (n := n) (X := X) (p := p) data
      (castForm hkp ω) Z
  else
    0

/-- Integration of degree-2p forms is linear. -/
theorem integrateDegree2p_linear (k : ℕ) (Z : Set X) (data : SubmanifoldIntegrationData n X)
    (c : ℝ) (ω₁ ω₂ : SmoothForm n X k) :
    integrateDegree2p (n := n) (X := X) k Z (c • ω₁ + ω₂) data =
      c * integrateDegree2p (n := n) (X := X) k Z ω₁ data +
        integrateDegree2p (n := n) (X := X) k Z ω₂ data := by
  unfold integrateDegree2p
  split_ifs with hk
  · have hkp : k = 2 * (k / 2) := Nat.eq_mul_of_div_eq_right hk rfl
    have hcast :
        castForm hkp (c • ω₁ + ω₂) =
          c • castForm hkp ω₁ + castForm hkp ω₂ := by
      calc
        castForm hkp (c • ω₁ + ω₂)
            = castForm hkp (c • ω₁) + castForm hkp ω₂ := by
                simpa [castForm_add]
        _ = c • castForm hkp ω₁ + castForm hkp ω₂ := by
              simp [castForm_smul]
    have h :=
      submanifoldIntegral_linear (n := n) (X := X) (p := k / 2) data Z c
        (castForm hkp ω₁) (castForm hkp ω₂)
    simpa [hcast] using h
  · simp only [MulZeroClass.mul_zero, add_zero]

/-- Integration on the empty set is zero. -/
theorem integrateDegree2p_empty (k : ℕ) (ω : SmoothForm n X k)
    (data : SubmanifoldIntegrationData n X) :
    integrateDegree2p (n := n) (X := X) k (∅ : Set X) ω data = 0 := by
  unfold integrateDegree2p
  split_ifs with hk
  · apply submanifoldIntegral_empty (n := n) (X := X) (p := k / 2) data
  · rfl

/-!
For even degree `k = 2 * p`, `integrateDegree2p` dispatches to `submanifoldIntegral`
(after an index-cast of the form degree).

This was previously tracked as a documentation stub; it will be reinstated
as an actual lemma once the degree-cast bookkeeping is stabilized in the integration layer. -/

/-- Integration of zero on the empty set is zero. -/
theorem submanifoldIntegral_zero_empty {p : ℕ} (data : SubmanifoldIntegrationData n X) :
    submanifoldIntegral (n := n) (X := X) (p := p) data (0 : SmoothForm n X (2 * p)) ∅ = 0 := by
  apply submanifoldIntegral_empty (n := n) (X := X) (p := p) data

/-- **Submanifold integration is bounded**. -/
theorem submanifoldIntegral_bound {p : ℕ} (data : SubmanifoldIntegrationData n X)
    (Z : Set X) (ω : SmoothForm n X (2 * p)) :
    |submanifoldIntegral (n := n) (X := X) (p := p) data ω Z| ≤
      (hausdorffMeasure2p (n := n) (X := X) p data Z).toReal * ‖ω‖ := by
  apply submanifoldIntegral_abs_le (n := n) (X := X) (p := p) data

/-- **Degree-2p integration is bounded**. -/
theorem integrateDegree2p_bound (k : ℕ) (Z : Set X) (ω : SmoothForm n X k)
    (data : SubmanifoldIntegrationData n X) :
    |integrateDegree2p (n := n) (X := X) k Z ω data| ≤
      (hausdorffMeasure2p (n := n) (X := X) (k / 2) data Z).toReal * ‖ω‖ := by
  unfold integrateDegree2p
  by_cases hk : 2 ∣ k
  · simp only [hk, ↓reduceDIte]
    have hkp : k = 2 * (k / 2) := Nat.eq_mul_of_div_eq_right hk rfl
    have h :=
      submanifoldIntegral_abs_le (n := n) (X := X) (p := k / 2) data (ω := castForm hkp ω) Z
    have hnorm : ‖castForm hkp ω‖ = ‖ω‖ := castForm_norm hkp ω
    simpa [hnorm] using h
  · simp only [hk, ↓reduceDIte, abs_zero]
    apply mul_nonneg
    · exact ENNReal.toReal_nonneg
    · exact comass_nonneg ω

end
