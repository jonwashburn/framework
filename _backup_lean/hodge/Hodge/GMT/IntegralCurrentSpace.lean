import Hodge.Analytic.IntegralCurrents

/-!
# GMT: Integral Current Space (wrapper)

Integral currents are defined in `Hodge.Analytic.IntegralCurrents`.  This file provides
some lightweight “space of integral currents with bounded mass” definitions under the
`Hodge.GMT` module hierarchy referenced in the operational plan.
-/

noncomputable section

open Classical

set_option autoImplicit false

namespace Hodge.GMT

/-- Boundary mass of an integral current.

For `k = 0`, we define this as `0` (there is no boundary in negative degree).
For `k = k' + 1`, this is the mass of the boundary current. -/
def bdryMass {n : ℕ} {X : Type*}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X] :
    (k : ℕ) → IntegralCurrent n X k → ℝ :=
  fun k T =>
    match k with
    | 0 => 0
    | k' + 1 => Current.mass (Current.boundary (k := k') T.toFun)

/-- Boundary mass with an implicit degree parameter (convenience wrapper). -/
abbrev bdryMass' {n : ℕ} {X : Type*} {k : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X]
    (T : IntegralCurrent n X k) : ℝ :=
  bdryMass (n := n) (X := X) k T

/-- Integral currents whose mass and boundary mass are bounded by `M`. -/
def BoundedIntegralCurrents {n : ℕ} {X : Type*} (k : ℕ) (M : ℝ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X] :
    Set (IntegralCurrent n X k) :=
  { T | Current.mass T.toFun ≤ M ∧ bdryMass (n := n) (X := X) k T ≤ M }

end Hodge.GMT
