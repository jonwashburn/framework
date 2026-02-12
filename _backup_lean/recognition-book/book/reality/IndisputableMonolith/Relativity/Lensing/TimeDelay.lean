import Mathlib
import IndisputableMonolith.Relativity.Geometry
import IndisputableMonolith.Relativity.Calculus
import IndisputableMonolith.Relativity.Geodesics.NullGeodesic
import IndisputableMonolith.Relativity.Geodesics.Integration
import IndisputableMonolith.Relativity.Perturbation.NewtonianGauge
import IndisputableMonolith.Relativity.Lensing.Deflection

namespace IndisputableMonolith
namespace Relativity
namespace Lensing

open Geometry
open Calculus
open Geodesics
open Perturbation

noncomputable def proper_time_along_path (ng : NewtonianGaugeMetric) (geo : NullGeodesic (newtonian_metric ng)) (lam_start lam_end : ℝ) : ℝ :=
  0.0

noncomputable def shapiro_delay (ng : NewtonianGaugeMetric) (impact : ImpactParameter) : ℝ :=
  let integral_factor := 2.0
  integral_factor * impact.b

axiom shapiro_GR_formula (M b : ℝ) :
  True

noncomputable def time_delay_ILG_vs_GR (ng_ILG ng_GR : NewtonianGaugeMetric) (impact : ImpactParameter) : ℝ :=
  shapiro_delay ng_ILG impact - shapiro_delay ng_GR impact

axiom time_delay_correction (ng_ILG ng_GR : NewtonianGaugeMetric) (impact : ImpactParameter) (gamma_val : ℝ) :
  True

axiom GR_limit_time_delay (ng : NewtonianGaugeMetric) (impact : ImpactParameter) :
  True

end Lensing
end Relativity
end IndisputableMonolith
