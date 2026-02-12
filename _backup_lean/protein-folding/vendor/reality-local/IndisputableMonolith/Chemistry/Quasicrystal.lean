import Mathlib
import IndisputableMonolith.Constants

/-!
Quasicrystal stability proxy at the golden ratio ratio.

We encode a simple convex energy proxy minimized at the golden ratio
ratio r = 1/φ. This supports a minimal, compiling stability statement
usable by certificates and reports without extra analysis machinery.
-/

namespace IndisputableMonolith
namespace Chemistry

noncomputable def phi_ratio : ℝ := 1 / Constants.phi

/-- Convex energy proxy minimized at `phi_ratio`. -/
noncomputable def tiling_energy (x : ℝ) : ℝ := (x - phi_ratio) ^ 2

/-- Stability: energy is minimized at the golden ratio ratio. -/
theorem quasicrystal_stable (x : ℝ) : tiling_energy phi_ratio ≤ tiling_energy x := by
  dsimp [tiling_energy, phi_ratio]
  -- Left side is 0^2 = 0; right side is a square hence ≥ 0
  have : (0 : ℝ) ≤ (x - (1 / Constants.phi)) ^ 2 := by
    exact sq_nonneg _
  simpa using this

end Chemistry
end IndisputableMonolith
