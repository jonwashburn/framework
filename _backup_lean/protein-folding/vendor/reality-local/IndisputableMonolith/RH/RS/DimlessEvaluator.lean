import IndisputableMonolith.RH.RS.Core
import IndisputableMonolith.RH.RS.Spec

namespace IndisputableMonolith
namespace RH
namespace RS

/-!
# DimlessEvaluator (interface)

`dimlessPack_explicit` is currently the designated **spec-level placeholder evaluator** for
bridge/ledger → dimensionless pack.

To make the future “derive the evaluator from real bridge/ledger structure” step clean and
non-invasive, we centralize the evaluation function behind a small interface:

* `DimlessEvaluator φ` – supplies an `eval` function producing a `DimlessPack` from any `(L,B)`.
* `explicitEvaluator φ` – the current default implementation (wraps `dimlessPack_explicit`).

Certified code should avoid treating `explicitEvaluator` as inevitable/derived; that’s tracked
as an open expansion target in `docs/BRIDGE_PROOFS_CHECKLIST.md`.
-/

/-- Interface: an evaluator that produces a bridge-side dimensionless pack at scale `φ`. -/
structure DimlessEvaluator (φ : ℝ) where
  eval : (L : Ledger) → (B : Bridge L) → DimlessPack L B

/-- The current designated evaluator (placeholder): wraps `dimlessPack_explicit`. -/
noncomputable def explicitEvaluator (φ : ℝ) : DimlessEvaluator φ :=
  { eval := fun L B => dimlessPack_explicit φ L B }

/-- MatchesEval re-expressed through an explicit evaluator object (for future swapping). -/
def MatchesEvalWith (E : DimlessEvaluator φ) (L : Ledger) (B : Bridge L) (U : UniversalDimless φ) : Prop :=
  PackMatches (φ:=φ) (P:=E.eval L B) U

@[simp] lemma matchesEvalWith_explicit (φ : ℝ) (L : Ledger) (B : Bridge L) :
    MatchesEvalWith (φ:=φ) (explicitEvaluator φ) L B (UD_explicit φ) := by
  simp [MatchesEvalWith, explicitEvaluator, PackMatches, dimlessPack_explicit, UD_explicit]

end RS
end RH
end IndisputableMonolith
