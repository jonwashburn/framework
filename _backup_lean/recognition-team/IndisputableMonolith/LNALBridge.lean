import Mathlib
import IndisputableMonolith.Octave.Theorem
import IndisputableMonolith.LNAL.ScheduleRSGray8
import IndisputableMonolith.LNAL.Invariants

/-!
# Octave ↔ LNAL Bridge (workstream D completion slice)

This module connects the canonical “octave” objects (`Phase = Fin 8`, Gray-8 order)
to the LNAL scheduler artifacts:

- `LNAL.ScheduleRSGray8.gray8At` is the same Gray-8 order as `Patterns.gray8At`.
- LNAL’s neutrality theorems (e.g. `LNAL.Invariants.neutral_every_8th_from0`) are
  exposed under the `Octave` namespace for certificate mapping.

Claim hygiene:
- Theorems here are purely internal to the formal model (no empirical inputs).
- Any interpretation of LNAL as physics/biology is outside this module.
-/

namespace IndisputableMonolith
namespace Octave
namespace LNALBridge

open IndisputableMonolith.Patterns

abbrev Phase := Octave.Phase

/-! ## Gray-8 order agreement -/

theorem lnal_gray8At_eq_patterns_gray8At (w : Fin 8) :
    IndisputableMonolith.LNAL.gray8At w = Patterns.gray8At w := by
  -- Both are the explicit [0,1,3,2,6,7,5,4] cycle; prove by finite case split.
  fin_cases w <;> decide

/-! ## Optional deepening: relate the full Gray-8 path and its Nat encoding -/

theorem lnal_gray8At_injective : Function.Injective IndisputableMonolith.LNAL.gray8At := by
  intro i j hij
  have hij' : Patterns.gray8At i = Patterns.gray8At j := by
    calc
      Patterns.gray8At i = IndisputableMonolith.LNAL.gray8At i := (lnal_gray8At_eq_patterns_gray8At i).symm
      _ = IndisputableMonolith.LNAL.gray8At j := hij
      _ = Patterns.gray8At j := (lnal_gray8At_eq_patterns_gray8At j)
  exact Patterns.gray8At_injective hij'

theorem patterns_grayCycle3Path_eq_lnal_pattern3 (w : Fin 8) :
    Patterns.grayCycle3Path w = Patterns.pattern3 (IndisputableMonolith.LNAL.gray8At w) := by
  -- unfold the path and rewrite the codeword via the Gray-8 agreement
  simp [Patterns.grayCycle3Path, (lnal_gray8At_eq_patterns_gray8At w).symm]

theorem toNat3_grayCycle3Path_eq_lnal_gray8At_val (w : Fin 8) :
    Patterns.toNat3 (Patterns.grayCycle3Path w) = (IndisputableMonolith.LNAL.gray8At w).val := by
  -- `toNat3 (pattern3 x) = x.val`, and `x = gray8At w`
  simp [Patterns.grayCycle3Path, Patterns.toNat3_pattern3, (lnal_gray8At_eq_patterns_gray8At w).symm]

/-! ## Re-export: LNAL neutrality at 8-boundaries -/

-- We keep the statements exactly as in `LNAL.Invariants`, but expose them through `Octave`.
abbrev neutral_every_8th_from0 :=
  IndisputableMonolith.LNAL.neutral_every_8th_from0

end LNALBridge
end Octave
end IndisputableMonolith
