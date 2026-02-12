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

/-!
Shapiro delay formula (GR) (documentation / TODO).
-/

noncomputable def time_delay_ILG_vs_GR (ng_ILG ng_GR : NewtonianGaugeMetric) (impact : ImpactParameter) : ℝ :=
  shapiro_delay ng_ILG impact - shapiro_delay ng_GR impact

/-!
Time-delay correction from ILG vs GR (documentation / TODO).
-/

/-!
GR limit of the time-delay expression (documentation / TODO).
-/

end Lensing
end Relativity
end IndisputableMonolith
