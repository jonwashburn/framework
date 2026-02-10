import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Measurement.WindowNeutrality

/-!
# Periodic Table Engine (fit‑free scaffold)

Octave ↔ eight‑tick mapping for chemistry: φ‑tier rails with a fixed set of
block offsets (s/p/d/f) and an eight‑window neutrality predicate used to detect
"rests" (noble‑gas closures). No per‑element tuning is permitted.

This file provides a minimal, zero‑parameter API surface to build downstream
predictions and falsifiers without binding to datasets yet.
-/

namespace IndisputableMonolith
namespace Chemistry
namespace PeriodicTable

open scoped BigOperators

/- Electronic blocks used for φ‑packing. -/
inductive Block | s | p | d | f deriving DecidableEq, Repr

/- Fixed φ‑packing offsets for blocks (no per‑element tuning). -/
class BlockOffsets where
  offset : Block → ℤ

namespace BlockOffsets
/- Default φ‑packing offsets (audit subject to change): s=0, p=1, d=2, f=3. -/
def default : BlockOffsets :=
  { offset := fun b =>
      match b with
      | Block.s => 0
      | Block.p => 1
      | Block.d => 2
      | Block.f => 3 }
end BlockOffsets

noncomputable section

/-- Default instance: s=0, p=1, d=2, f=3 (no per‑element tuning). -/
instance : BlockOffsets := BlockOffsets.default

/- Dimensionless shell rail multiplier (E_n/E_coh) at rail n: φ^{2n}. -/
def railFactor (n : ℤ) : ℝ :=
  Real.rpow IndisputableMonolith.Constants.phi ((2 : ℝ) * (n : ℝ))

/- Predicted (dimensionless) band multiplier for block `b` on rail `n`.
     Uses fixed φ‑packing offsets from `BlockOffsets`. -/
def blockFactor (n : ℤ) (b : Block) [B : BlockOffsets] : ℝ :=
  let exp : ℝ := (2 : ℝ) * (n : ℝ) + (B.offset b : ℝ)
  Real.rpow IndisputableMonolith.Constants.phi exp

/-- Rail energy (dimensionful): E_n = E_coh · φ^{2n}. -/
def railEnergy (n : ℤ) : ℝ :=
  IndisputableMonolith.Constants.E_coh * railFactor n

/- Sliding 8‑window sum used for neutrality tests. -/
def window8Sum (f : ℕ → ℝ) (Z0 : ℕ) : ℝ :=
  (Finset.range 8).sum (fun k => f (Z0 + k))

/-! Minimal indexing scaffold

Maps atomic number `Z` to a coarse rail/block index to enable a fit‑free
band predictor. This is a placeholder indexer; the final mapping will be a
deterministic, data‑independent rule consistent with φ‑tiers and block counts.
-/
structure Index where
  rail  : ℤ
  block : Block
  deriving Repr

/- Placeholder indexer from atomic number (deterministic, no tuning). -/
def indexOf (Z : ℕ) : Index :=
  let period : ℕ := (Z - 1) / 8
  let pos    : ℕ := (Z - 1) % 8
  let b : Block :=
    match pos with
    | 0 | 1      => Block.s
    | 2 | 3 | 4  => Block.p
    | 5 | 6      => Block.d
    | _          => Block.f
  { rail := (period : ℤ), block := b }

/- Dimensionless predicted band multiplier for atomic number `Z`. -/
def bandMultiplier (Z : ℕ) [BlockOffsets] : ℝ :=
  let idx := indexOf Z
  blockFactor idx.rail idx.block

/-- Predicted (dimensionful) band energy for atomic number `Z`.
    This is a fit‑free display using the universal coherence tick. -/
def bandEnergy (Z : ℕ) [BlockOffsets] : ℝ :=
  IndisputableMonolith.Constants.E_coh * bandMultiplier Z

/- Eight‑window neutrality predicate (rest if the sum is zero in aligned windows).
     In practice, the neutrality test is applied to a fit‑free valence‑cost proxy. -/
def neutralAt (f : ℕ → ℝ) (Z0 : ℕ) : Prop :=
  window8Sum f Z0 = 0

/-- Trivial sanity: a constant‑zero proxy is neutral on any aligned 8‑window. -/
theorem neutralAt_const_zero (Z0 : ℕ) :
  neutralAt (fun _ => (0 : ℝ)) Z0 := by
  unfold neutralAt window8Sum
  simpa using (by
    have : (Finset.range 8).sum (fun _ => (0 : ℝ)) = 0 := by
      simpa using (Finset.sum_const_zero (Finset.range 8))
    exact this)

end
end PeriodicTable
end Chemistry
end IndisputableMonolith
