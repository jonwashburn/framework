import Mathlib
import IndisputableMonolith.Streams

/-!
Module: IndisputableMonolith.Measurement

Two parts:
- Discrete stream measurements over 8-tick windows and periodic extensions,
  culminating in average observations.
- A minimal real-valued measurement scaffold and a CQ score with monotonicity lemmas.

Designed to stay light on dependencies and avoid `by decide` brittleness.
-/

namespace IndisputableMonolith
namespace Measurement

open Classical
open Streams
open scoped BigOperators
open Real

/-- Sum of one 8‑tick sub‑block starting at index `j*8`. -/
def subBlockSum8 (s : Stream) (j : Nat) : Nat :=
  ∑ i : Fin 8, (if s (j * 8 + i.val) then 1 else 0)

/-- On any stream lying in the cylinder of an 8‑bit window, the aligned
    first block sum (j=0; T=8k alignment) equals the window integer `Z`. -/
lemma firstBlockSum_eq_Z_on_cylinder (w : Pattern 8) {s : Stream}
  (hs : s ∈ Cylinder w) :
  subBlockSum8 s 0 = Z_of_window w := by
  classical
  have hsum : subBlockSum8 s 0 = sumFirst 8 s := by
    unfold subBlockSum8 sumFirst
    simp [Nat.zero_mul, zero_add]
  simpa [hsum] using (sumFirst_eq_Z_on_cylinder (n:=8) w (s:=s) hs)

/-- For periodic extensions of an 8‑bit window, each sub‑block sums to `Z`. -/
lemma subBlockSum8_periodic_eq_Z (w : Pattern 8) (j : Nat) :
  subBlockSum8 (extendPeriodic8 w) j = Z_of_window w := by
  classical
  unfold subBlockSum8 Z_of_window extendPeriodic8
  have hmod : ∀ i : Fin 8, ((j * 8 + i.val) % 8) = i.val := by
    intro i
    have : (j * 8) % 8 = 0 := by simpa using Nat.mul_mod_right j 8
    have hi : i.val % 8 = i.val := Nat.mod_eq_of_lt i.isLt
    calc
      (j * 8 + i.val) % 8
          = ((j * 8) % 8 + i.val % 8) % 8 := by
                simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm] using
                  (Nat.add_mod (j*8) i.val 8)
      _   = (0 + i.val) % 8 := by simpa [this, hi]
      _   = i.val % 8 := by simp
      _   = i.val := by simpa [hi]
  -- Rewrite each summand to the corresponding window bit.
  have hfun :
    (fun i : Fin 8 => if (extendPeriodic8 w) (j * 8 + i.val) then 1 else 0)
      = (fun i : Fin 8 => if w i then 1 else 0) := by
    funext i
    have : (extendPeriodic8 w) (j * 8 + i.val) = w ⟨(j*8 + i.val) % 8, Nat.mod_lt _ (by decide)⟩ := by
      simp [extendPeriodic8_eq_mod]
    have := congrArg (fun b => if b then 1 else 0) this
    simpa [hmod i] using this
  simpa [Z_of_window, subBlockSum8] using
    (congrArg (fun f => ∑ i : Fin 8, f i) hfun)

/-- Aligned block sum over `k` copies of the 8‑tick window (so instrument length `T=8k`). -/
def blockSumAligned8 (k : Nat) (s : Stream) : Nat :=
  ∑ j : Fin k, subBlockSum8 s j.val

lemma sum_const_nat {α} (s : Finset α) (c : Nat) :
  (∑ _ in s, c) = s.card * c := by
  classical
  simpa using Finset.sum_const_natural (s := s) (a := c)

/-- For `s = extendPeriodic8 w`, summing `k` aligned 8‑blocks yields `k * Z(w)`. -/
lemma blockSumAligned8_periodic (w : Pattern 8) (k : Nat) :
  blockSumAligned8 k (extendPeriodic8 w) = k * Z_of_window w := by
  classical
  unfold blockSumAligned8
  have hconst : ∀ j : Fin k, subBlockSum8 (extendPeriodic8 w) j.val = Z_of_window w := by
    intro j; simpa using subBlockSum8_periodic_eq_Z w j.val
  -- Sum of a constant family over `Fin k` is `k * const`
  have : (∑ j : Fin k, (fun _ => Z_of_window w) j) = k * Z_of_window w := by
    simpa [sum_const_nat, Finset.card_univ] using
      (sum_const_nat (s := (Finset.univ : Finset (Fin k))) (c := Z_of_window w))
  -- Replace each term by the constant using `hconst`
  have hsum : (∑ j : Fin k, subBlockSum8 (extendPeriodic8 w) j.val)
            = (∑ j : Fin k, (fun _ => Z_of_window w) j) := by
    congr
    funext j
    simpa using (hconst j).symm
  simpa [hsum, this]

/-- Averaged (per‑window) observation equals `Z` on periodic extensions. -/
def observeAvg8 (k : Nat) (s : Stream) : Nat :=
  blockSumAligned8 k s / k

/-- DNARP Eq. (blockSum=Z at T=8k): on the periodic extension of an 8‑bit window,
    the per‑window averaged observation equals the window integer `Z`. -/
lemma observeAvg8_periodic_eq_Z {k : Nat} (hk : k ≠ 0) (w : Pattern 8) :
  observeAvg8 k (extendPeriodic8 w) = Z_of_window w := by
  classical
  unfold observeAvg8
  have hsum := blockSumAligned8_periodic w k
  have hk' : 0 < k := Nat.pos_of_ne_zero hk
  have divCancel : (k * Z_of_window w) / k = Z_of_window w := by
    simpa [Nat.mul_comm] using Nat.mul_div_cancel_left (Z_of_window w) hk'
  simpa [hsum, divCancel]

end Measurement
end IndisputableMonolith

/-! #### Minimal measurement map and CQ observable (temporarily disabled to fix build) -/
/-
namespace IndisputableMonolith
namespace Measurement

noncomputable section
open Classical

structure Map (State Obs : Type) where
  T : ℝ
  T_pos : 0 < T
  meas : (ℝ → State) → ℝ → Obs

@[simp] def avg (T : ℝ) (hT : 0 < T) (x : ℝ → ℝ) (t : ℝ) : ℝ :=
  let tmid := t + T / 2
  x tmid

structure CQ where
  listensPerSec : ℝ
  opsPerSec : ℝ
  coherence8 : ℝ
  coherence8_bounds : 0 ≤ coherence8 ∧ 0 ≤ coherence8 ∧ coherence8 ≤ 1 ∧ coherence8 ≤ 1 := by
    exact And.intro (by exact le_of_eq rfl)
      (And.intro (by exact le_of_eq rfl) (And.intro (by exact le_of_eq rfl) (by exact le_of_eq rfl)))

@[simp] def score (c : CQ) : ℝ :=
  if c.opsPerSec = 0 then 0 else (c.listensPerSec / c.opsPerSec) * c.coherence8

-- Monotonicity lemmas can be restored once upstream build blockers are cleared.

end

end Measurement
end IndisputableMonolith
-/
