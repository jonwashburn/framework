import Mathlib
import IndisputableMonolith.LNAL.VM
import IndisputableMonolith.LNAL.JBudget
import IndisputableMonolith.Measurement
import IndisputableMonolith.Patterns.GrayCode
import IndisputableMonolith.LedgerUnits

/-!
# RS-Gray-8 Scheduler (T = 8) for Photonic Control

This module defines an eight-phase Gray scheduler for `T = 8` and proves
the exact-cover and neutrality-style identities needed by Recognition Science:

- Exact cover of the 3-bit pattern classes in one period (T6)
- A mirrored-half δ-window identity implying Σ₀⁷ δᵢ = 0 (neutral window)
- A simple RS-aware per-window J aggregation compatible with `JBudget`

The construction uses the canonical 3-bit binary-reflected Gray cycle:

  [0, 1, 3, 2, 6, 7, 5, 4]

This visits each 3-bit pattern exactly once and wraps to form a cycle.
-/

namespace IndisputableMonolith
namespace LNAL

open Classical

/-- Canonical 3-bit Gray cycle for `T = 8`. -/
@[simp] def gray8Cycle : Array (Fin 8) :=
  #[(0 : Fin 8), 1, 3, 2, 6, 7, 5, 4]

/-- The Gray-8 cycle has length 8. -/
lemma gray8_len : gray8Cycle.size = 8 := rfl

/-- Gray index at window `w` (0 ≤ w < 8). -/
@[simp] def gray8At (w : Fin 8) : Fin 8 :=
  gray8Cycle[w.val]!

/-- No duplicates in the Gray-8 cycle (exact cover as a list). -/
lemma gray8_nodup : gray8Cycle.toList.Nodup := by
  -- Direct enumeration for robustness
  decide

/-- The Gray-8 cycle is a permutation of `Fin 8`. -/
theorem gray8_exactCover : (gray8Cycle.toList.map (fun i => i.val)).Nodup ∧
    (List.eraseDups (gray8Cycle.toList.map (fun i => i.val))).length = 8 := by
  decide

/-- A mirrored-half δ window implies neutrality: if δ₍i+4₎ = -δᵢ for i=0..3,
    then the total sum Σ₀⁷ δᵢ = 0. -/
theorem mirrored_halves_delta_neutral
    (δ : Fin 8 → ℤ)
    (h0 : δ 0 = -δ 4)
    (h1 : δ 1 = -δ 5)
    (h2 : δ 2 = -δ 6)
    (h3 : δ 3 = -δ 7) :
    (∑ i : Fin 8, δ i) = 0 := by
  classical
  -- Pairwise cancellations from the mirror hypothesis
  have hc0 : δ 0 + δ 4 = 0 := by linarith [h0]
  have hc1 : δ 1 + δ 5 = 0 := by linarith [h1]
  have hc2 : δ 2 + δ 6 = 0 := by linarith [h2]
  have hc3 : δ 3 + δ 7 = 0 := by linarith [h3]
  -- Regroup the sum into mirrored pairs (abelian-group normalization handles associativity/commutativity).
  have hregroup :
      (∑ i : Fin 8, δ i) =
        (δ 0 + δ 4) +
        (δ 1 + δ 5) +
        (δ 2 + δ 6) +
        (δ 3 + δ 7) := by
    -- Expand the finite sum, then normalize.
    simp [Fin.sum_univ_succ]
    abel
  -- Conclude by substituting the pair cancellations.
  calc
    (∑ i : Fin 8, δ i) =
        (δ 0 + δ 4) +
        (δ 1 + δ 5) +
        (δ 2 + δ 6) +
        (δ 3 + δ 7) := hregroup
    _ = 0 := by simp [hc0, hc1, hc2, hc3]

/-- RS-style per-window J aggregation based on positive instruction costs.
    This mirrors `JBudget.deltaJPerWindow` but is exposed as part of the
    RS Gray-8 scheduler API for convenience. -/
@[simp] def rsDeltaJPerWindow (code : Array LInstr) : Array Nat :=
  deltaJPerWindow code

/-- A compact per-window schedule record for RS Gray-8. -/
structure Gray8Window where
  window : Nat
  gray   : Nat
  deltaJ : Nat
deriving Repr, DecidableEq

/-- Construct the Gray-8 schedule annotation from code. -/
def rsGray8Schedule (code : Array LInstr) : List Gray8Window :=
  let deltas := rsDeltaJPerWindow code
  let windows := deltas.size
  (List.range windows).map fun w =>
    let g : Nat := (gray8At ⟨w % 8, by
      have : w % 8 < 8 := Nat.mod_lt _ (by decide)
      simpa using this⟩).val
    let dJ : Nat := (deltas[w]? ).getD 0
    { window := w, gray := g, deltaJ := dJ }

end LNAL
end IndisputableMonolith
