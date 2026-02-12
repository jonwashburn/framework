import Mathlib
import IndisputableMonolith.RecogSpec.Bands

/-(
Dimension forcing via CRT logic (8↔45 hinge)

Reframe: the minimal period 2^D co‑synchronizes with the 45‑fold structure
only at 360. Conclude the only D with lcm(2^D, 45) = 360 (respecting atomic
ledger periods) is D = 3.
)-/

namespace IndisputableMonolith
namespace Verification
namespace DimensionCRT

open Nat

/-- Chinese‑remainder style dimension forcing: only D=3 satisfies
    lcm(2^D, 45) = 360. This packages the 8↔45 hinge as an arithmetic lemma. -/
theorem lcm_pow2_45_forces_D3 (D : ℕ)
    (h : Nat.lcm (2 ^ D) 45 = 360) : D = 3 := by
  -- Reuse the canonical equivalence provided by the RS stack.
  exact (IndisputableMonolith.RecogSpec.lcm_pow2_45_eq_iff D).mp h

/-- Equivalence form convenient for automation. -/
theorem lcm_pow2_45_eq_360_iff (D : ℕ) :
    Nat.lcm (2 ^ D) 45 = 360 ↔ D = 3 :=
  IndisputableMonolith.RecogSpec.lcm_pow2_45_eq_iff D

end DimensionCRT
end Verification
end IndisputableMonolith
