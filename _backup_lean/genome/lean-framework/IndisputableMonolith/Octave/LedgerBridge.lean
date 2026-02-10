import Mathlib
import IndisputableMonolith.Octave.Theorem
import IndisputableMonolith.LedgerPostingAdjacency

/-!
# Octave ↔ Ledger Bridge (workstream B surface)

This module provides a clean, certificate-ready bridge statement:

> Under a “single posting per tick” ledger constraint (`PostingStep`), the induced
> parity observation evolves by **one-bit Gray adjacency** each tick.

Claim hygiene:
- The adjacency theorem is **THEOREM**-level once `PostingStep` is accepted as the step rule.
- Proving that RS *forces* `PostingStep` is a separate Workstream B obligation
  (it will be explicitly labeled MECH/AXIOM/DERIVED once implemented).
-/

namespace IndisputableMonolith
namespace Octave
namespace LedgerBridge

open IndisputableMonolith.Patterns

abbrev Side := LedgerPostingAdjacency.Side
abbrev LedgerState (d : Nat) := LedgerPostingAdjacency.LedgerState d
abbrev parity (d : Nat) := LedgerPostingAdjacency.parity d
abbrev PostingStep (d : Nat) := LedgerPostingAdjacency.PostingStep (d := d)
abbrev LegalAtomicTick (d : Nat) := LedgerPostingAdjacency.LegalAtomicTick (d := d)
abbrev MonotoneLedger (d : Nat) := LedgerPostingAdjacency.MonotoneLedger (d := d)
noncomputable abbrev ledgerL1Cost (d : Nat) := LedgerPostingAdjacency.ledgerL1Cost (d := d)
noncomputable abbrev ledgerJlogCost (d : Nat) := LedgerPostingAdjacency.ledgerJlogCost (d := d)

theorem postingStep_implies_grayAdj {d : Nat} {L L' : LedgerState d}
    (h : PostingStep d L L') :
    OneBitDiff (parity d L) (parity d L') :=
  LedgerPostingAdjacency.postingStep_oneBitDiff (d := d) h

theorem postingStep_iff_legalAtomicTick {d : Nat} {L L' : LedgerState d} :
    PostingStep d L L' ↔ LegalAtomicTick d L L' :=
  LedgerPostingAdjacency.postingStep_iff_legalAtomicTick (d := d)

theorem legalAtomicTick_implies_grayAdj {d : Nat} {L L' : LedgerState d}
    (h : LegalAtomicTick d L L') :
    OneBitDiff (parity d L) (parity d L') :=
  LedgerPostingAdjacency.legalAtomicTick_oneBitDiff (d := d) h

theorem minCost_monotoneStep_implies_postingStep {d : Nat} [NeZero d]
    {L L' : LedgerState d}
    (hmono : MonotoneLedger d L L')
    (hneq : L ≠ L')
    (hmin : ∀ L'' : LedgerState d, MonotoneLedger d L L'' → L ≠ L'' →
      ledgerL1Cost d L L' ≤ ledgerL1Cost d L L'') :
    PostingStep d L L' :=
  LedgerPostingAdjacency.minCost_monotoneStep_implies_postingStep (d := d)
    (L := L) (L' := L') hmono hneq hmin

theorem postingStep_of_monotone_and_ledgerJlogCost_le_Jlog1 {d : Nat} {L L' : LedgerState d}
    (hmono : MonotoneLedger d L L')
    (hneq : L ≠ L')
    (hle : ledgerJlogCost d L L' ≤ Cost.Jlog (1 : ℝ)) :
    PostingStep d L L' :=
  LedgerPostingAdjacency.postingStep_of_monotone_and_ledgerJlogCost_le_Jlog1 (d := d)
    (L := L) (L' := L') hmono hneq hle

theorem minJlogCost_monotoneStep_implies_postingStep {d : Nat} [NeZero d]
    {L L' : LedgerState d}
    (hmono : MonotoneLedger d L L')
    (hneq : L ≠ L')
    (hmin : ∀ L'' : LedgerState d, MonotoneLedger d L L'' → L ≠ L'' →
      ledgerJlogCost d L L' ≤ ledgerJlogCost d L L'') :
    PostingStep d L L' :=
  LedgerPostingAdjacency.minJlogCost_monotoneStep_implies_postingStep (d := d)
    (L := L) (L' := L') hmono hneq hmin

/-! ## Workstream B tightening: AtomicTick-parameterized bridge -/

/-- If RS provides a per-tick *atomic* posted account (via `Recognition.AtomicTick`) and a side schedule,
then the induced tick update changes parity in exactly one bit. -/
theorem atomicTickStep_implies_grayAdj {d : Nat}
    [IndisputableMonolith.Recognition.AtomicTick (LedgerPostingAdjacency.AccountRS d)]
    (sideAt : Nat → Side) (t : Nat) (L : LedgerState d) :
    OneBitDiff (parity d L) (parity d (LedgerPostingAdjacency.stepAt (d := d) sideAt t L)) :=
  LedgerPostingAdjacency.stepAt_oneBitDiff (d := d) sideAt t L

end LedgerBridge
end Octave
end IndisputableMonolith
