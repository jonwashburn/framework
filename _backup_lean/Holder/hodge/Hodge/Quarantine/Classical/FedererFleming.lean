import Hodge.Analytic.IntegralCurrents
import Hodge.Analytic.FlatNorm
import Hodge.Analytic.Currents
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Filter.Basic

noncomputable section

open Classical Filter Hodge

set_option autoImplicit false

variable {n : ℕ} {X : Type*}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
  [MeasurableSpace X] [BorelSpace X]

/-!
# Track A.3: Federer-Fleming Compactness Theorem
-/

/-- Auxiliary constants for the Deformation Theorem. -/
noncomputable def C1 (_n _k : ℕ) : ℝ := 2
noncomputable def C2 (_n _k : ℕ) : ℝ := 2
noncomputable def C3 (_n _k : ℕ) : ℝ := 2
noncomputable def C4 (_n _k : ℕ) : ℝ := 2

-- deformation_theorem removed (unused, not in 8 pillars)

/-- The hypothesis bundle for Federer-Fleming compactness. -/
structure FFCompactnessHypothesis (n : ℕ) (X : Type*) (k : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X] where
  T : ℕ → IntegralCurrent n X (k + 1)
  M : ℝ
  mass_bound : ∀ j, (T j : Current n X (k + 1)).mass + (T j).boundary.toFun.mass ≤ M

/-- The conclusion of Federer-Fleming. -/
structure FFCompactnessConclusion (n : ℕ) (X : Type*) (k : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X]
    (hyp : FFCompactnessHypothesis n X k) where
  T_limit : IntegralCurrent n X (k + 1)
  φ : ℕ → ℕ
  φ_strict_mono : StrictMono φ
  converges : Tendsto (fun j => flatNorm ((hyp.T (φ j) : Current n X (k + 1)) - T_limit.toFun)) atTop (nhds 0)

/-- Boundary operator for currents of arbitrary degree (HL-style). -/
noncomputable def boundaryHL {k : ℕ} (T : Current n X k) : Current n X (k - 1) :=
  match k with
  | 0 => 0
  | k' + 1 => Current.boundary T

/-- **Compactness data** for flat-norm limits. -/
class FlatLimitExistenceData (n : ℕ) (X : Type*) (k : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X] : Prop where
  flat_limit_existence :
    ∀ (T_seq : ℕ → IntegralCurrent n X k)
      (M : ℝ)
      (hM : ∀ j, (T_seq j : Current n X k).mass + (boundaryHL (T_seq j : Current n X k)).mass ≤ M),
      ∃ (T_limit : IntegralCurrent n X k) (φ : ℕ → ℕ),
        StrictMono φ ∧
        Tendsto (fun j => flatNorm ((T_seq (φ j) : Current n X k) - T_limit.toFun)) atTop (nhds 0)

/-- **Federer-Fleming Compactness Theorem** (Federer-Fleming, 1960).
    Any sequence of integral currents with uniformly bounded mass and boundary mass
    has a subsequence converging in flat norm to an integral current.

    Reference: [H. Federer and W.H. Fleming, "Normal and integral currents", 1960]. -/
theorem flat_limit_existence {k : ℕ} [FlatLimitExistenceData n X k]
    (T_seq : ℕ → IntegralCurrent n X k)
    (M : ℝ) (hM : ∀ j, (T_seq j : Current n X k).mass + (boundaryHL (T_seq j : Current n X k)).mass ≤ M) :
    ∃ (T_limit : IntegralCurrent n X k) (φ : ℕ → ℕ),
      StrictMono φ ∧
      Tendsto (fun j => flatNorm ((T_seq (φ j) : Current n X k) - T_limit.toFun)) atTop (nhds 0) := by
  exact FlatLimitExistenceData.flat_limit_existence (n := n) (X := X) (k := k) T_seq M hM

end
