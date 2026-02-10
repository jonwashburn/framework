import Mathlib
import IndisputableMonolith.Genetics.QualiaOptimization
import IndisputableMonolith.ULQ.Core

/-!
# Genetics ↔ ULQ bridge (MODEL)

`Genetics/QualiaOptimization.lean` defines a 6-bit “qualia point” `Q₆ := Fin 6 → Bool`
derived from codons. ULQ defines `QualiaSpace` as `(mode, intensity, valence, temporal)`.

This module provides an explicit **MODEL** bridge:

- `QualiaPoint (Q₆)` → `ULQ.QualiaSpace`
- `Codon` → `ULQ.QualiaSpace` via `codon_to_qualia`

Claim hygiene:
- This mapping is **not derived** from RS; it is an explicit modeling/interpretation layer.
- It exists to remove the “disconnected” status of the Genetics Q₆ mapping and make the bridge
  explicit and auditable.
- Replace this mapping once a principled derivation is agreed (or keep it as a named MODEL).
-/

namespace IndisputableMonolith
namespace Genetics

open QualiaOptimization
open ULQ

namespace ULQBridge

open scoped BigOperators

private def i0 : Fin 6 := ⟨0, by decide⟩
private def i1 : Fin 6 := ⟨1, by decide⟩
private def i2 : Fin 6 := ⟨2, by decide⟩
private def i3 : Fin 6 := ⟨3, by decide⟩
private def i4 : Fin 6 := ⟨4, by decide⟩
private def i5 : Fin 6 := ⟨5, by decide⟩

/-- Convert a Bool bit to Nat {0,1}. -/
def bit (b : Bool) : Nat := if b then 1 else 0

/-- Interpret the first three Q₆ bits as a 3-bit natural number (0..7). -/
def modeBits (p : QualiaPoint) : Nat :=
  (if p i0 then 4 else 0) + (if p i1 then 2 else 0) + (if p i2 then 1 else 0)

lemma modeBits_le_7 (p : QualiaPoint) : modeBits p ≤ 7 := by
  have h0 : (if p i0 then 4 else 0) ≤ 4 := by by_cases h : p i0 <;> simp [h]
  have h1 : (if p i1 then 2 else 0) ≤ 2 := by by_cases h : p i1 <;> simp [h]
  have h2 : (if p i2 then 1 else 0) ≤ 1 := by by_cases h : p i2 <;> simp [h]
  have := add_le_add (add_le_add h0 h1) h2
  simpa [modeBits] using this

/-- MODEL: pick a non-DC mode index in {1..7} from the Q₆ bits.

We interpret the 3-bit value; if it is 0 we map it to 1 to satisfy ULQ neutrality. -/
def modeIndex (p : QualiaPoint) : Nat :=
  let n := modeBits p
  if n = 0 then 1 else n

lemma modeIndex_lt_8 (p : QualiaPoint) : modeIndex p < 8 := by
  classical
  unfold modeIndex
  set n := modeBits p
  by_cases h : n = 0
  · simp [h]
  · have hn : n ≤ 7 := by simpa [n] using modeBits_le_7 p
    have hnlt : n < 8 := lt_of_le_of_lt hn (by norm_num)
    simpa [h] using hnlt

lemma modeIndex_ne_zero (p : QualiaPoint) : modeIndex p ≠ 0 := by
  unfold modeIndex
  set n := modeBits p
  by_cases h : n = 0
  · simp [h]
  · simp [h]

/-- The ULQ mode derived (as a MODEL) from a Q₆ point. -/
def qualiaModeOfQ6 (p : QualiaPoint) : QualiaMode :=
  let k : Fin 8 := ⟨modeIndex p, modeIndex_lt_8 p⟩
  have hk : k.val ≠ 0 := by
    -- `k.val = modeIndex p`
    simpa [k] using modeIndex_ne_zero p
  ⟨k, hk⟩

/-- Interpret the next two Q₆ bits as a 2-bit intensity level (0..3). -/
def intensityBits (p : QualiaPoint) : Nat :=
  (if p i3 then 2 else 0) + (if p i4 then 1 else 0)

lemma intensityBits_lt_4 (p : QualiaPoint) : intensityBits p < 4 := by
  have h3 : (if p i3 then 2 else 0) ≤ 2 := by by_cases h : p i3 <;> simp [h]
  have h4 : (if p i4 then 1 else 0) ≤ 1 := by by_cases h : p i4 <;> simp [h]
  have hsum : intensityBits p ≤ 3 := by
    have := add_le_add h3 h4
    simpa [intensityBits] using this
  exact lt_of_le_of_lt hsum (by norm_num)

def intensityLevelOfQ6 (p : QualiaPoint) : IntensityLevel :=
  ⟨⟨intensityBits p, intensityBits_lt_4 p⟩⟩

/-- MODEL: valence sign from the last Q₆ bit. -/
def valenceOfQ6 (p : QualiaPoint) : HedonicValence :=
  let v : ℝ := if p i5 then 1 else -1
  ⟨v, by
    by_cases h : p i5 <;> simp [v, h]⟩

/-- MODEL: temporal quality from the raw 3-bit mode value (0..7). -/
def temporalOfQ6 (p : QualiaPoint) : TemporalQuality :=
  ⟨⟨modeBits p, lt_of_le_of_lt (modeBits_le_7 p) (by norm_num)⟩⟩

/-- MODEL: interpret a Q₆ point as a ULQ qualia space point. -/
def qualiaOfQ6 (p : QualiaPoint) : QualiaSpace :=
  { mode := qualiaModeOfQ6 p
  , intensity := intensityLevelOfQ6 p
  , valence := valenceOfQ6 p
  , temporal := temporalOfQ6 p
  }

/-- MODEL: interpret a codon’s Q₆ point as ULQ qualia. -/
def qualiaOfCodon (c : Codon) : QualiaSpace :=
  qualiaOfQ6 (codon_to_qualia c)

end ULQBridge

end Genetics
end IndisputableMonolith
