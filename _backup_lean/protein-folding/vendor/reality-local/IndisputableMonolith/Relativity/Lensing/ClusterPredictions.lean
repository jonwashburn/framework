import Mathlib
import IndisputableMonolith.Relativity.Geometry
import IndisputableMonolith.Relativity.Lensing.Deflection
import IndisputableMonolith.Relativity.Lensing.TimeDelay
import IndisputableMonolith.Relativity.PostNewtonian.GammaExtraction

namespace IndisputableMonolith
namespace Relativity
namespace Lensing

open Geometry
open PostNewtonian

structure ClusterModel where
  mass : ℝ
  radius : ℝ
  rho : ℝ → ℝ

noncomputable def cluster_deflection (cluster : ClusterModel) (impact : ImpactParameter) (gamma_val : ℝ) : ℝ :=
  spherical_lens_deflection cluster.mass gamma_val impact.b

noncomputable def multiple_images (cluster : ClusterModel) (source_position : ℝ) (gamma_val : ℝ) : List ℝ :=
  []

noncomputable def image_time_delays (cluster : ClusterModel) (images : List ℝ) (gamma_val : ℝ) : List ℝ :=
  []

/-!
Cluster lensing bands (documentation / TODO).
-/

/-!
Strong lensing test (documentation / TODO).
-/

end Lensing
end Relativity
end IndisputableMonolith
