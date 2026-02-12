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

/-- Gray index at window `w` (0 ≤ w < 8). -/
@[simp] def gray8At (w : Fin 8) : Fin 8 := gray8Cycle.get! w.val

/-- The Gray-8 cycle has length 8. -/
lemma gray8_len : gray8Cycle.size = 8 := rfl

/-- No duplicates in the Gray-8 cycle (exact cover as a list). -/
lemma gray8_nodup : gray8Cycle.toList.Nodup := by
  -- Direct enumeration for robustness
  decide

/-- The Gray-8 cycle is a permutation of `Fin 8`. -/
theorem gray8_exactCover : (gray8Cycle.toList.map (fun i => i.val)).Nodup ∧
    (List.eraseDups (gray8Cycle.toList.map (fun i => i.val))).length = 8 := by
  -- `Nodup` is immediate from `gray8_nodup` and evaluation; the deduplicated
  -- image length equals 8 by direct computation.
  have h₁ : gray8Cycle.toList.Nodup := gray8_nodup
  have hmap : (gray8Cycle.toList.map (fun i => i.val)).Nodup := by
    exact List.nodup_map (fun _ _ h => by cases h; rfl) h₁
  refine And.intro hmap ?hlen
  -- Evaluate eraseDups length by computation
  -- The list is [0,1,3,2,6,7,5,4]; all distinct
  decide

/-- A mirrored-half δ window implies neutrality: if δ₍i+4₎ = -δᵢ for i=0..3,
    then the total sum Σ₀⁷ δᵢ = 0. -/
theorem mirrored_halves_delta_neutral
    (δ : Fin 8 → ℤ)
    (hmirror : ∀ i : Fin 4, δ ⟨i, by decide⟩ = -δ ⟨i + 4, by decide⟩) :
    (∑ i : Fin 8, δ i) = 0 := by
  classical
  -- Pairwise cancellations from the mirror hypothesis
  have h0 : δ ⟨0, by decide⟩ + δ ⟨4, by decide⟩ = 0 := by
    have := hmirror ⟨0, by decide⟩; linarith
  have h1 : δ ⟨1, by decide⟩ + δ ⟨5, by decide⟩ = 0 := by
    have := hmirror ⟨1, by decide⟩; linarith
  have h2 : δ ⟨2, by decide⟩ + δ ⟨6, by decide⟩ = 0 := by
    have := hmirror ⟨2, by decide⟩; linarith
  have h3 : δ ⟨3, by decide⟩ + δ ⟨7, by decide⟩ = 0 := by
    have := hmirror ⟨3, by decide⟩; linarith
  -- Expand the finite sum explicitly
  have hexpand : (∑ i : Fin 8, δ i) =
      δ ⟨0, by decide⟩ + δ ⟨1, by decide⟩ + δ ⟨2, by decide⟩ + δ ⟨3, by decide⟩ +
      δ ⟨4, by decide⟩ + δ ⟨5, by decide⟩ + δ ⟨6, by decide⟩ + δ ⟨7, by decide⟩ := by
    simp [Fin.sum_univ_succ]
  -- Regroup and cancel each mirrored pair
  have : (∑ i : Fin 8, δ i) =
      (δ ⟨0, by decide⟩ + δ ⟨4, by decide⟩) +
      (δ ⟨1, by decide⟩ + δ ⟨5, by decide⟩) +
      (δ ⟨2, by decide⟩ + δ ⟨6, by decide⟩) +
      (δ ⟨3, by decide⟩ + δ ⟨7, by decide⟩) := by
    simpa [hexpand, add_comm, add_left_comm, add_assoc]
  simpa [this, h0, h1, h2, h3]

/-- RS-style per-window J aggregation based on positive instruction costs.
    This mirrors `JBudget.deltaJPerWindow` but is exposed as part of the
    RS Gray-8 scheduler API for convenience. -/
@[simp] def rsDeltaJPerWindow (code : Array LInstr) : Array Nat :=
  JBudget.deltaJPerWindow code

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
    { window := w, gray := g, deltaJ := deltas.get! w }

end LNAL
end IndisputableMonolith
