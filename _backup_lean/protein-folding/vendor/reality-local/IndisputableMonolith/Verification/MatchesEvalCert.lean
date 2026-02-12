import Mathlib
import IndisputableMonolith.RH.RS.Spec

/-!
# MatchesEval Certificate (computed matching, non-existential)

This certificate packages the lemma `IndisputableMonolith.RH.RS.matchesEval_explicit`:
for every ledger/bridge, the designated computed evaluator `dimlessPack_explicit`
matches the explicit universal target `UD_explicit`.

This is an **audit** certificate: it records that certified reasoning about “matches”
routes through `RH.RS.MatchesEval` (computed) rather than the existential `RH.RS.Matches`.
-/

namespace IndisputableMonolith
namespace Verification
namespace MatchesEval

open IndisputableMonolith.RH

structure MatchesEvalCert where
  deriving Repr

@[simp] def MatchesEvalCert.verified (_c : MatchesEvalCert) : Prop :=
  ∀ (φ : ℝ) (L : RH.RS.Ledger) (B : RH.RS.Bridge L),
    RH.RS.MatchesEval φ L B (RH.RS.UD_explicit φ)

@[simp] theorem MatchesEvalCert.verified_any (c : MatchesEvalCert) :
    MatchesEvalCert.verified c := by
  intro φ L B
  exact RH.RS.matchesEval_explicit φ L B

end MatchesEval
end Verification
end IndisputableMonolith
