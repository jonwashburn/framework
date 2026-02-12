import Hodge.GMT.Current
import Hodge.GMT.IntegrationCurrent
import Hodge.GMT.FlatNormTopology
import Hodge.GMT.PoincareDuality

/-!
# GMT Tests (Round 3)

This file is a lightweight compilation/typecheck suite for the Agent‑5 GMT layer.
It is not imported by the proof-track entry point.
-/

noncomputable section

open Classical Hodge Hodge.GMT

set_option autoImplicit false

universe u

variable {n : ℕ} {X : Type u}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X]

/-! ## Basic smoke tests -/

-- Test 1: linearity of evaluation for integration currents (data-first).
example (p : ℕ) (data : ClosedSubmanifoldData n X (2 * p))
    (c : ℝ) (ω₁ ω₂ : SmoothForm n X (2 * p)) :
    (integrationCurrent_data (n := n) (X := X) p data).toFun (c • ω₁ + ω₂) =
      c * (integrationCurrent_data (n := n) (X := X) p data).toFun ω₁ +
        (integrationCurrent_data (n := n) (X := X) p data).toFun ω₂ :=
  integrationCurrent_linear_data (n := n) (X := X) (p := p) (c := c) data ω₁ ω₂

-- Test 2: boundary operator typechecks.
example {k : ℕ} (T : DeRhamCurrent n X k) : DeRhamCurrent n X (k - 1) :=
  DeRhamCurrent.boundary (n := n) (X := X) (k := k) T

-- Test 3: real-valued flat norm is nonnegative.
example {k : ℕ} (T : Current n X k) :
    0 ≤ _root_.flatNorm (n := n) (X := X) (k := k) T :=
  _root_.flatNorm_nonneg (n := n) (X := X) (k := k) T

-- Test 4: Poincaré dual form constructor typechecks.
example (p : ℕ) (data : ClosedSubmanifoldData n X (2 * p))
    [CurrentRegularizationData n X (2 * p)] : SmoothForm n X (2 * p) :=
  poincareDualForm_construct (n := n) (X := X) (p := p) data

/-! ## Round 7 Tests: Current Architecture -/

-- Test 6: ClosedSubmanifoldData.toIntegrationData carries the set Z
example {k : ℕ} (data : ClosedSubmanifoldData n X k) :
    data.toIntegrationData.carrier = data.carrier := rfl

-- Test 7: integrateDegree2p now takes explicit SubmanifoldIntegrationData
example (k : ℕ) (Z : Set X) (ω : SmoothForm n X k)
    (data : SubmanifoldIntegrationData n X) :
    integrateDegree2p (n := n) (X := X) k Z ω data =
      integrateDegree2p (n := n) (X := X) k Z ω data := rfl

-- Test 8: integration current from explicit data agrees with the real constructor (definitional).
example (k : ℕ) (data : ClosedSubmanifoldData n X k) (ω : SmoothForm n X k) :
    (integrationCurrentK_data (n := n) (X := X) k data).toFun ω =
      (integrationCurrentReal_data (n := n) (X := X) k data).toFun ω := by
  rfl

-- Test 9: Distinct carriers remain distinct after converting to IntegrationData
example (k : ℕ) (data₁ data₂ : ClosedSubmanifoldData n X k)
    (hne : data₁.carrier ≠ data₂.carrier) :
    data₁.toIntegrationData.carrier ≠ data₂.toIntegrationData.carrier := by
  simpa using hne
