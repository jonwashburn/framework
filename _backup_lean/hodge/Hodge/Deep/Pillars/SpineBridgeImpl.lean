import Hodge.Classical.GAGA
import Hodge.Classical.GeometricCycleClass
import Hodge.Deep.Pillars.HarveyLawsonImpl

noncomputable section

open Classical Hodge Hodge.Deep.HarveyLawson

namespace Hodge.Deep.Pillars

variable {n : ℕ} {X : Type*}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X]

/--
**Spine Bridge Cohomology Axiom**

For every signed algebraic cycle Z, the geometric cycle class (computed via
regularization of the integration current over Z.support) equals the
de Rham cohomology class of Z.representingForm.

**Mathematical Content**: The bridge identity
  [FundamentalClass(Z)] = [γ]
follows from the chain:
1. Harvey-Lawson: Z was constructed from γ via calibration, so
   the integration current [Z] represents the same class as γ.
2. Regularization preserves cohomology: [regularize(T)] = [T].
3. Therefore the regularized form (which defines cycleClass_geom_data)
   is cohomologous to representingForm.

Reference: [Harvey-Lawson, "Calibrated Geometries", Acta Math. 148 (1982)],
[Federer, "Geometric Measure Theory", §4.1 (1969)],
[de Rham, "Variétés Différentiables", Ch. V (1955)].
-/
axiom spine_bridge_cohomology_eq {p : ℕ}
    [Hodge.GMT.CurrentRegularizationData n X (2 * p)]
    [CycleClass.PoincareDualityFromCurrentsData n X p]
    [SignedAlgebraicCycleSupportData n X p]
    (Z : SignedAlgebraicCycle n X p) :
    Z.cycleClass_geom_data = ofForm Z.representingForm Z.representingForm_closed

/--
**Spine Bridge Instance**

Provides the `SpineBridgeData_data` instance required for the deep track.
Uses the spine bridge cohomology axiom asserting that the geometric cycle class
equals the class of the representing form.
-/
instance instSpineBridgeData_data {p : ℕ}
    [Hodge.GMT.CurrentRegularizationData n X (2 * p)]
    [CycleClass.PoincareDualityFromCurrentsData n X p]
    [SignedAlgebraicCycleSupportData n X p] :
    SpineBridgeData_data n X p where
  fundamental_eq_representing := fun Z =>
    spine_bridge_cohomology_eq Z

end Hodge.Deep.Pillars
