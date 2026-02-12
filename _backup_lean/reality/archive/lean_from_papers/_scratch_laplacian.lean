import Mathlib
import IndisputableMonolith.Relativity.Calculus.Derivatives

namespace IndisputableMonolith
namespace Relativity
namespace Calculus

open Real

/-- The Laplacian of 1/r is zero away from the origin. -/
theorem laplacian_radialInv_zero_proof {C : ℝ} {x : Fin 4 → ℝ} (hx : spatialRadius x ≠ 0) :
    laplacian (fun y => C * radialInv 1 y) x = 0 := by
  unfold laplacian radialInv spatialRadius spatialNormSq
  -- This requires many steps of chain rule
  sorry

end Calculus
end Relativity
end IndisputableMonolith
