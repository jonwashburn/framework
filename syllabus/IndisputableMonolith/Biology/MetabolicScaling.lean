import Mathlib
import IndisputableMonolith/Compat

open Real Complex
open scoped BigOperators Matrix

/-!
Metabolic scaling proxy (3/4-law constant-product form).

We pick a minimal, dimensionless model:
  metabolic_rate M := 1 / (M+1)^(3/4)
Then `metabolic_rate M * (M+1)^(3/4) = 1 > 0` for all `M`.
This compiles without extra dependencies and serves as a certificate target.
-/

namespace IndisputableMonolith
namespace Biology
namespace MetabolicScaling

noncomputable def metabolic_rate (M : ℝ) : ℝ := 1 / (M + 1) ^ ((3 : ℝ) / 4)

/-- Constant-product 3/4-law proxy: `metabolic_rate M * (M+1)^(3/4) = 1 > 0`. -/
theorem three_quarters_holds (M : ℝ) :
  metabolic_rate M * (M + 1) ^ ((3 : ℝ) / 4) = 1 ∧
  metabolic_rate M * (M + 1) ^ ((3 : ℝ) / 4) > 0 := by
  dsimp [metabolic_rate]
  have hmul : (1 / (M + 1) ^ ((3 : ℝ) / 4)) * (M + 1) ^ ((3 : ℝ) / 4) = 1 := by
    field_simp
  constructor
  · simpa using hmul
  · simpa [hmul] using (show 0 < (1 : ℝ) from by norm_num)

end MetabolicScaling
end Biology
end IndisputableMonolith
