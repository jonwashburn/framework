import Mathlib
import IndisputableMonolith.Nuclear.MagicNumbers

/-!
# Magic Numbers Derivation (Scaffold)

This module is the **Phase FQ1** scaffold for upgrading nuclear magic numbers
from a hardcoded list to a theorem derived from a ledger topology model.

**Current status:** we formalize the *derivation pipeline* (shell gaps -> closures)
and provide a canonical instance matching the observed sequence. The remaining
work is to replace the canonical gaps with a construction forced by minimal
ledger axioms.

See:
- `planning/MAGIC_NUMBER_DERIVATION_STATUS.md`
- `planning/FUSION_FISSION_RESEARCH_EXECUTION_PLAN.md`
-/

namespace IndisputableMonolith
namespace Nuclear
namespace MagicNumbersDerivation

open Nuclear.MagicNumbers

/-! ## Generic closure construction -/

/-- Given shell gaps, the induced closure sequence is the cumulative sum (dropping the initial 0). -/
def closuresOfGaps (gaps : List ℕ) : List ℕ :=
  (gaps.scanl (· + ·) 0).tail

theorem closuresOfGaps_eq_scanl_tail (gaps : List ℕ) :
    closuresOfGaps gaps = (gaps.scanl (· + ·) 0).tail := by
  rfl

/-! ## A minimal model interface (no axioms, just a record) -/

/-- A shell model supplies a gap list (to be derived later from ledger topology). -/
structure ShellModel where
  shellGaps : List ℕ
  shellGaps_pos : ∀ g, g ∈ shellGaps → 0 < g

/-- The closure list predicted by a shell model. -/
def ShellModel.closures (M : ShellModel) : List ℕ :=
  closuresOfGaps M.shellGaps

/-- A number is magic in the model iff it is a closure. -/
def ShellModel.isMagic (M : ShellModel) (n : ℕ) : Prop :=
  n ∈ M.closures

/-! ## Ledger-driven gap rule (start of the *real* derivation)

This section introduces a small interface for producing shell gaps from a rule.
The intent is to later constrain `gap` by minimal ledger-topology axioms (8-tick
neutrality / closure conditions), so that the resulting closures are forced.
-/

/-- A ledger-driven gap rule produces a (potentially infinite) shell-gap sequence. -/
structure LedgerGapRule where
  gap : ℕ → ℕ
  gap_pos : ∀ k, 0 < gap k

/-- The first `n` gaps from a rule. -/
def LedgerGapRule.firstNGaps (R : LedgerGapRule) (n : ℕ) : List ℕ :=
  (List.range n).map R.gap

theorem LedgerGapRule.mem_firstNGaps_iff (R : LedgerGapRule) (n : ℕ) (g : ℕ) :
    g ∈ R.firstNGaps n ↔ ∃ k < n, R.gap k = g := by
  unfold LedgerGapRule.firstNGaps
  constructor
  · intro hg
    rcases List.mem_map.mp hg with ⟨k, hk, rfl⟩
    rcases List.mem_range.mp hk with hk'
    exact ⟨k, hk', rfl⟩
  · rintro ⟨k, hk, rfl⟩
    apply List.mem_map_of_mem
    exact List.mem_range.mpr hk

/-- Build a finite `ShellModel` from the first `n` gaps of a rule. -/
def LedgerGapRule.toShellModel (R : LedgerGapRule) (n : ℕ) : ShellModel where
  shellGaps := R.firstNGaps n
  shellGaps_pos := by
    intro g hg
    rcases (LedgerGapRule.mem_firstNGaps_iff R n g).1 hg with ⟨k, _hk, hkEq⟩
    simpa [hkEq] using R.gap_pos k

/-! ## Canonical model (matches the currently observed sequence) -/

/-- The canonical shell model uses the existing `Nuclear.MagicNumbers.shellGaps`. -/
def canonicalModel : ShellModel where
  shellGaps := shellGaps
  shellGaps_pos := by
    intro g hg
    -- `shellGaps` is the explicit list `[2, 6, 12, 8, 22, 32, 44]`.
    simp [shellGaps] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem canonicalModel_closures :
    canonicalModel.closures = magicNumbers := by
  -- This is exactly `shell_gaps_sum_to_magic`, re-expressed via `closuresOfGaps`.
  unfold ShellModel.closures canonicalModel closuresOfGaps
  simpa using (shell_gaps_sum_to_magic)

theorem canonical_isMagic_iff (n : ℕ) :
    canonicalModel.isMagic n ↔ Nuclear.MagicNumbers.isMagic n := by
  unfold ShellModel.isMagic Nuclear.MagicNumbers.isMagic
  simpa [canonicalModel_closures]

end MagicNumbersDerivation
end Nuclear
end IndisputableMonolith
