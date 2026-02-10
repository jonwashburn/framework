import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
import IndisputableMonolith.ProteinFolding.NativeFold
import IndisputableMonolith.ProteinFolding.NativeFoldProof
import IndisputableMonolith.ProteinFolding.Basic.EightBeatCycle
import IndisputableMonolith.ProteinFolding.Coercivity.CPMCoercivity

/-!
# Verification: Native Fold Theorem for Minimal Peptide Chains

This module provides a concrete verification of the Native Fold Theorem
for a minimal 2-residue peptide chain.

## The Model

1. **System**: A 2-residue peptide.
2. **Conformation**: Represented by a single ledger window (the coupling between the two residues).
3. **Native State**: A conformation where the ledger window is perfectly balanced (zero strain).
4. **Target**: Prove that the native state minimizes the $Q_6$ functional.
-/

namespace IndisputableMonolith
namespace ProteinFolding
namespace Verification
namespace MinimalPeptide

open Constants
open Cost
open NativeFold
open NativeFoldProof
open EightBeatCycle
open Coercivity

/-- **Minimal Peptide Conformation**
    A 2-residue peptide with a single interaction window. -/
def minimal_peptide (w : LedgerWindow) : Conformation where
  numResidues := 2
  dihedrals := fun _ => (0, 0)
  rotamers := fun _ => []
  windows := [w]
  window_count_match := by simp

/-- **Conformation to Windows for Minimal Peptide**
    (Retires Axiom A6) -/
theorem minimal_peptide_to_windows_proven (w : LedgerWindow) :
    conformation_to_windows (minimal_peptide w) = [w] := rfl

/-- **Native Minimal Peptide**
    The native state is a perfectly balanced (zero cost) ledger window. -/
def native_window : ValidLedgerWindow := zeroLedger

def native_peptide : Conformation := minimal_peptide native_window.toLedgerWindow

/-- **Energy of Minimal Peptide** -/
theorem minimal_peptide_energy (w : LedgerWindow) :
    recognition_energy (minimal_peptide w) = ∑ k : Beat, w.costs k := by
  unfold recognition_energy Q6
  rw [minimal_peptide_to_windows_proven]
  simp

/-- **Native State has Zero Energy** -/
theorem native_peptide_energy_zero :
    recognition_energy native_peptide = 0 := by
  unfold native_peptide
  rw [minimal_peptide_energy]
  simp [native_window, zeroLedger, ValidLedgerWindow.toLedgerWindow]

/-- **Positivity of Recognition Energy**
    In the RS model, the energy (sum of J-costs) is non-negative for positive scale ratios.
    (Retires Axiom A7) -/
theorem beat_costs_nonneg_proven (w : LedgerWindow) (k : Beat) :
    (∀ b : Beat, w.ratios b > 0) → 0 ≤ w.costs k := by
  intro h_pos
  -- w.costs k is defined as Jcost (w.ratios k).
  -- Jcost is non-negative for all positive inputs (AM-GM).
  exact Cost.Jcost_nonneg (h_pos k)

/-- **Minimal Peptide Minimization**
    The native peptide (zero strain) minimizes the recognition energy for any 2-residue chain.
    (Grounded in Cost.Jcost_nonneg) -/
theorem native_peptide_is_min :
    ∀ (w : LedgerWindow), (∀ k, w.ratios k > 0) →
    recognition_energy native_peptide ≤ recognition_energy (minimal_peptide w) := by
  intro w h_pos
  rw [native_peptide_energy_zero, minimal_peptide_energy]
  apply Finset.sum_nonneg
  intro k _
  exact beat_costs_nonneg_proven w k h_pos

/-- **Verification Result**
    The Native Fold Theorem holds for the minimal 2-residue peptide chain.
    (Retires Axioms A6, A7) -/
theorem minimal_peptide_verification :
    ∃ (c_native : Conformation), c_native.numResidues = 2 ∧
    ∀ (c : Conformation), c.numResidues = 2 → (∀ w ∈ c.windows, ∀ k, w.ratios k > 0) →
    recognition_energy c_native ≤ recognition_energy c := by
  use native_peptide
  constructor
  · rfl
  · intro c h_num h_pos
    -- Since numResidues = 2, there is exactly one window by window_count_match
    have h_len := c.window_count_match
    rw [h_num] at h_len
    -- windows.length = 1
    obtain ⟨w, hw⟩ := List.length_eq_one.mp h_len
    have h_win : c.windows = [w] := hw

    rw [native_peptide_energy_zero, recognition_energy, Q6, h_win]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    apply Finset.sum_nonneg
    intro k _
    apply beat_costs_nonneg_proven
    intro k'
    exact h_pos w (by rw [h_win]; simp) k'

end MinimalPeptide
end Verification
end ProteinFolding
end IndisputableMonolith
