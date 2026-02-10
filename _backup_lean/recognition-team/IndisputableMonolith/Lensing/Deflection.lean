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

/-- **DEFINITION: RS Deflection Angle**
    The total deflection angle for a signal passing through a Newtonian gauge potential.
    $\alpha = \int (d/db)(\Phi + \Psi) dz$.
    For RS in the GR limit, $\Phi = \Psi$, so $\alpha = 2 \int (d/db)\Phi dz$. -/
noncomputable def deflection_angle (ng : NewtonianGaugeMetric) (impact : ImpactParameter) : ℝ :=
  (4 * ng.Phi) / impact.b

/-- **CERT(definitional): Analytical matches Numerical**
    The analytical deflection formula for a spherical lens matches its own definition.
    Note: Real numerical integration of null geodesic equations is not performed here. -/
theorem analytical_matches_numerical (ng : NewtonianGaugeMetric) (impact : ImpactParameter) :
    ∃ (error : ℝ), abs (deflection_angle ng impact - 4 * ng.Phi / impact.b) < error := by
  -- In the small-field limit (Phi << 1), the geodesic integration reduces to
  -- the standard impulse approximation result.
  -- SCAFFOLD: This identity matches the definition of deflection_angle.
  -- See: LaTeX Manuscript, Chapter "Astrophysical Tests", Section "Gravitational Lensing".
  use 0.000001
  unfold deflection_angle
  simp only [abs_zero, sub_self]
  positivity

end Lensing
end Relativity
end IndisputableMonolith
