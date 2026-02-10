import Mathlib
import IndisputableMonolith.Constants

/-!
# Eight-Beat Cycle and Ledger Neutrality

This module formalizes the 8-tick ledger cycle that governs protein folding dynamics.

## Key Concepts

1. **Ledger Neutrality**: The sum of J-costs over any complete 8-tick window must equal zero.
2. **Neutral Windows**: Large topology changes can only occur at beats 0 and 4.
3. **360-Iteration Superperiod**: LCM(8, 45) = 360 defines the full coherence cycle.

## Physical Motivation

The 8-beat cycle arises from the fundamental recognition architecture. Each beat
represents a phase of the recognition-decoherence cycle, with beats 0 and 4 being
"neutral windows" where large conformational changes are permitted without
disrupting ledger coherence.

-/

namespace IndisputableMonolith
namespace ProteinFolding
namespace EightBeatCycle

open Constants

/-! ## The 8-Beat Structure -/

/-- The 8-tick cycle phase -/
abbrev Beat := Fin 8

/-- A complete 8-tick ledger window (raw, not necessarily balanced) -/
structure LedgerWindow where
  /-- J-cost contributions at each tick -/
  costs : Beat → ℝ

/-- A valid (balanced) ledger window where costs sum to zero.

    This is the fundamental constraint from the recognition axiom:
    any complete 8-tick cycle must leave the ledger balanced.

    Physical interpretation: Energy borrowed in early beats must be
    repaid by later beats within the same window. -/
structure ValidLedgerWindow where
  /-- J-cost contributions at each tick -/
  costs : Beat → ℝ
  /-- The fundamental balance constraint -/
  balanced : (∑ k : Beat, costs k) = 0

/-- Convert valid ledger to raw ledger -/
def ValidLedgerWindow.toLedgerWindow (v : ValidLedgerWindow) : LedgerWindow :=
  ⟨v.costs⟩

/-- **LEDGER NEUTRALITY THEOREM**

    For any valid ledger window, the sum of J-costs equals zero.
    This is now definitional rather than axiomatic. -/
theorem ledger_neutrality (L : ValidLedgerWindow) :
    (∑ k : Beat, L.costs k) = 0 := L.balanced

/-- Construct a valid ledger from costs that demonstrably sum to zero -/
def mkValidLedger (costs : Beat → ℝ) (h : (∑ k : Beat, costs k) = 0) : ValidLedgerWindow :=
  ⟨costs, h⟩

/-- The trivial balanced ledger (all zeros) -/
def zeroLedger : ValidLedgerWindow where
  costs := fun _ => 0
  balanced := by simp

/-- A neutral window is a beat where topology changes are allowed -/
def isNeutralWindow (beat : Beat) : Bool := beat.val = 0 ∨ beat.val = 4

/-- Neutral windows are exactly beats 0 and 4 -/
theorem neutral_windows_are_zero_and_four (beat : Beat) :
    isNeutralWindow beat ↔ beat.val ∈ ({0, 4} : Set ℕ) := by
  simp only [isNeutralWindow, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    cases h with
    | inl h0 => left; exact h0
    | inr h4 => right; exact h4
  · intro h
    cases h with
    | inl h0 => left; exact h0
    | inr h4 => right; exact h4

/-! ## Neutral Window Gating (D6) -/

/-- Topology move permission depends on neutral window and protein size.

    Small proteins (≤45 residues) can change topology at any beat.
    Large proteins require neutral windows for topology changes. -/
def topologyMoveAllowed (beat : Beat) (proteinSize : ℕ) (atPlateau : Bool) : Bool :=
  proteinSize ≤ 45 ∨ isNeutralWindow beat ∨ atPlateau

/-- Small proteins always have topology permission -/
theorem small_protein_always_allowed (beat : Beat) (n : ℕ) (hn : n ≤ 45) :
    topologyMoveAllowed beat n false = true := by
  simp only [topologyMoveAllowed, hn, true_or, Bool.true_eq_true]

/-- Large proteins require neutral windows (when not at plateau) -/
theorem large_protein_needs_window (beat : Beat) (n : ℕ) (hn : 45 < n)
    (hbeat : ¬isNeutralWindow beat) :
    topologyMoveAllowed beat n false = false := by
  simp only [topologyMoveAllowed, Bool.or_eq_true, Bool.false_eq_true, or_false]
  push_neg
  constructor
  · omega
  · exact hbeat

/-! ## 360-Iteration Superperiod -/

/-- The superperiod is LCM(8, 45) = 360 -/
def superperiod : ℕ := Nat.lcm 8 45

/-- The superperiod equals 360 -/
theorem superperiod_eq_360 : superperiod = 360 := by
  native_decide

/-- 8 divides the superperiod -/
theorem eight_divides_superperiod : 8 ∣ superperiod := by
  exact Nat.dvd_lcm_left 8 45

/-- 45 divides the superperiod -/
theorem fortyfive_divides_superperiod : 45 ∣ superperiod := by
  exact Nat.dvd_lcm_right 8 45

/-- The number of complete 8-beat cycles in a superperiod -/
def cyclesPerSuperperiod : ℕ := superperiod / 8

theorem cycles_per_superperiod_eq : cyclesPerSuperperiod = 45 := by
  native_decide

/-- The number of Gap-45 windows in a superperiod -/
def gap45WindowsPerSuperperiod : ℕ := superperiod / 45

theorem gap45_windows_eq : gap45WindowsPerSuperperiod = 8 := by
  native_decide

/-! ## Phase Relationships -/

/-- Convert iteration number to current beat -/
def currentBeat (iteration : ℕ) : Beat :=
  ⟨iteration % 8, Nat.mod_lt iteration (by norm_num)⟩

/-- Check if iteration is at a neutral window -/
def atNeutralWindow (iteration : ℕ) : Bool :=
  isNeutralWindow (currentBeat iteration)

/-- Check if iteration is at a superperiod boundary -/
def atSuperperiodBoundary (iteration : ℕ) : Bool :=
  iteration % superperiod = 0

/-- Neutral windows occur at iterations 0, 4, 8, 12, ... (mod 8 ∈ {0, 4}) -/
theorem neutral_window_pattern (n : ℕ) :
    atNeutralWindow n ↔ n % 8 = 0 ∨ n % 8 = 4 := by
  simp only [atNeutralWindow, isNeutralWindow, currentBeat]
  constructor
  · intro h
    cases h with
    | inl h0 => left; exact h0
    | inr h4 => right; exact h4
  · intro h
    cases h with
    | inl h0 => left; exact h0
    | inr h4 => right; exact h4

/-! ## Gray Code Encoding -/

/-- Gray code for a beat (used in β-sheet parity) -/
def grayCode (t : Beat) : ℕ := t.val ^^^ (t.val >>> 1)

/-- Gray code parity -/
def grayParity (t : Beat) : Bool := (grayCode t) % 2 = 1

/-- Gray codes for all 8 beats -/
theorem gray_code_table :
    grayCode ⟨0, by norm_num⟩ = 0 ∧
    grayCode ⟨1, by norm_num⟩ = 1 ∧
    grayCode ⟨2, by norm_num⟩ = 3 ∧
    grayCode ⟨3, by norm_num⟩ = 2 ∧
    grayCode ⟨4, by norm_num⟩ = 6 ∧
    grayCode ⟨5, by norm_num⟩ = 7 ∧
    grayCode ⟨6, by norm_num⟩ = 5 ∧
    grayCode ⟨7, by norm_num⟩ = 4 := by
  simp only [grayCode]
  native_decide

/-- Gray parities alternate in a specific pattern -/
theorem gray_parity_table :
    grayParity ⟨0, by norm_num⟩ = false ∧
    grayParity ⟨1, by norm_num⟩ = true ∧
    grayParity ⟨2, by norm_num⟩ = true ∧
    grayParity ⟨3, by norm_num⟩ = false ∧
    grayParity ⟨4, by norm_num⟩ = false ∧
    grayParity ⟨5, by norm_num⟩ = true ∧
    grayParity ⟨6, by norm_num⟩ = true ∧
    grayParity ⟨7, by norm_num⟩ = false := by
  simp only [grayParity, grayCode]
  native_decide

end EightBeatCycle
end ProteinFolding
end IndisputableMonolith
