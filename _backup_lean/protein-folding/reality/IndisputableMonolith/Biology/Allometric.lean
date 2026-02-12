import Mathlib

/-!
Allometric exponent proxy from dimensional tiling.

We define a simple exponent `(D)/(D+1)` and verify that for `D=3`
it equals `3/4`. This serves as a minimal compiling statement for
certificates and reports.
-/

namespace IndisputableMonolith
namespace Biology
namespace Allometric

noncomputable def allometric_exponent (D : Nat) : ℝ := (D : ℝ) / (D + 1 : ℝ)

@[simp] theorem allometric_holds : allometric_exponent 3 = (3 : ℝ) / (4 : ℝ) := by
  dsimp [allometric_exponent]
  norm_num

end Allometric
end Biology
end IndisputableMonolith
