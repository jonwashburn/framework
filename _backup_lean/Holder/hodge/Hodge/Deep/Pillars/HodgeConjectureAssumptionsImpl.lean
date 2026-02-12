import Hodge.Kahler.Main
import Hodge.Kahler.Microstructure
import Hodge.Deep.Pillars.FedererFlemingImpl
import Hodge.Deep.Pillars.HarveyLawsonImpl
import Hodge.Deep.Pillars.GAGAImpl
import Hodge.Deep.Pillars.SpineBridgeImpl
import Hodge.GMT.MollifierRegularization
import Hodge.Analytic.Integration.HausdorffIntegrationInst
import Hodge.Classical.PoincareDualityFromCurrents
import Hodge.Deep.Pillars.AlgebraicSupportImpl

noncomputable section

open Classical Hodge Hodge.Deep.Pillars

namespace Hodge.Deep

variable {n : ℕ} {X : Type*}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X]

/--
**Global Hodge Conjecture Assumptions Instance**

This provides the `HodgeConjectureAssumptions` instance globally,
using the scaffolded deep pillars.
This allows `hodge_conjecture'` to be used without explicit arguments.
-/
instance instHodgeConjectureAssumptions {p : ℕ} : HodgeConjectureAssumptions n X p :=
  {
    toAutomaticSYRData := AutomaticSYRData.universal
    toCurrentRegularizationData := inferInstance
    toPoincareDualityFromCurrentsData := inferInstance
    toAlgebraicSubvarietyClosedSubmanifoldData := inferInstance
    toSignedAlgebraicCycleSupportCodimData := inferInstance
    toSpineBridgeData_data := inferInstance
    toCalibratedCurrentRegularityData := inferInstance
    toHarveyLawsonKingData := inferInstance
    toChowGAGAData := inferInstance
  }

end Hodge.Deep
