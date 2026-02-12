import Mathlib
import IndisputableMonolith.RH.RS.Spec
import IndisputableMonolith.RH.RS.ClosureShim

/-!
# Recognition Closure Non-Vacuity Certificate

This certificate upgrades the RS “closure” story by explicitly asserting that the
closure bundle includes **proved** content (not just Prop-valued fields inside packs):

- the `UD_explicit φ` strong-CP witness holds,
- the 8-tick minimal witness holds,
- and the two-branch Born bridge holds.

These are packaged inside `RH.RS.Inevitability_dimless` (and thus inside
`RH.RS.Recognition_Closure`) so closure is not vacuously satisfied by merely carrying
unproven propositions.
-/

namespace IndisputableMonolith
namespace Verification
namespace RecognitionClosure

open IndisputableMonolith.RH

structure RecognitionClosureNonVacuityCert where
  deriving Repr

@[simp] def RecognitionClosureNonVacuityCert.verified (_c : RecognitionClosureNonVacuityCert) : Prop :=
  ∀ φ : ℝ,
    RH.RS.Recognition_Closure φ →
      (RH.RS.UD_explicit φ).strongCP0 ∧
      (RH.RS.UD_explicit φ).eightTick0 ∧
      (RH.RS.UD_explicit φ).born0

@[simp] theorem RecognitionClosureNonVacuityCert.verified_any (c : RecognitionClosureNonVacuityCert) :
    RecognitionClosureNonVacuityCert.verified c := by
  intro φ h
  -- `Recognition_Closure` is `Inevitability_dimless ∧ Inevitability_absolute`
  -- and `Inevitability_dimless` now carries the proven UD-explicit properties.
  exact h.left.right

end RecognitionClosure
end Verification
end IndisputableMonolith
