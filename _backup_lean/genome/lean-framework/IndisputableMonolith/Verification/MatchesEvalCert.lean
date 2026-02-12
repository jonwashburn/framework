import Mathlib
import IndisputableMonolith.RecogSpec.Spec

/-!
# MatchesEval Certificate (computed matching, non-existential)

This certificate packages the lemma `IndisputableMonolith.RecogSpec.matchesEval_explicit`:
for every ledger/bridge, the designated computed evaluator `dimlessPack_explicit`
matches the explicit universal target `UD_explicit`.

This is an **audit** certificate: it records that certified reasoning about “matches”
routes through `RecogSpec.MatchesEval` (computed) rather than the existential `RecogSpec.Matches`.
-/

namespace IndisputableMonolith
namespace Verification
namespace MatchesEval

open IndisputableMonolith.RecogSpec

structure MatchesEvalCert where
  deriving Repr

@[simp] def MatchesEvalCert.verified (_c : MatchesEvalCert) : Prop :=
  ∀ (φ : ℝ) (L : RecogSpec.Ledger) (B : RecogSpec.Bridge L),
    RecogSpec.MatchesEval φ L B (RecogSpec.UD_explicit φ)

@[simp] theorem MatchesEvalCert.verified_any (c : MatchesEvalCert) :
    MatchesEvalCert.verified c := by
  intro φ L B
  exact RecogSpec.matchesEval_explicit φ L B

end MatchesEval
end Verification
end IndisputableMonolith
