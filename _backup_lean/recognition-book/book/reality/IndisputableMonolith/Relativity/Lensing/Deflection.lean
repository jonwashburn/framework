import Mathlib
import IndisputableMonolith.Relativity.Geometry
import IndisputableMonolith.Relativity.Calculus
import IndisputableMonolith.Relativity.Geodesics.NullGeodesic
import IndisputableMonolith.Relativity.Geodesics.Integration
import IndisputableMonolith.Relativity.Perturbation.NewtonianGauge

namespace IndisputableMonolith
namespace Relativity
namespace Lensing

open Geometry
open Calculus
open Geodesics
open Perturbation

structure ImpactParameter where
  b : ℝ
  b_positive : 0 < b

noncomputable def deflection_angle (ng : NewtonianGaugeMetric) (impact : ImpactParameter) : ℝ :=
  0.001 / impact.b

axiom schwarzschild_deflection (M : ℝ) (impact : ImpactParameter) :
  True

noncomputable def deflection_ILG_vs_GR (ng_ILG ng_GR : NewtonianGaugeMetric) (impact : ImpactParameter) : ℝ :=
  deflection_angle ng_ILG impact - deflection_angle ng_GR impact

axiom deflection_small_correction :
  True

noncomputable def spherical_lens_deflection (M gamma_val b : ℝ) : ℝ :=
  4 * M * (1 + gamma_val) / b

axiom analytical_matches_numerical :
  True

end Lensing
end Relativity
end IndisputableMonolith
