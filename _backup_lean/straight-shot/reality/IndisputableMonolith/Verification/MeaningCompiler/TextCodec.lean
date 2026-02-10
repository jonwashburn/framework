import Mathlib
import IndisputableMonolith.Token.WTokenId

/-!
# Text/Byte → WToken Codec (Certified Acquisition Layer)

This module implements a **deterministic, invertible codec** that maps raw bytes
(`Fin 256`) to a stream of `Token.WTokenId` (20-symbol alphabet) using base-20
digits.

This is an **acquisition/IO layer**: it does *not* claim the resulting token
stream is a semantic decomposition; it only guarantees we can ingest classic text
corpora purely as `WTokenId`s, with Lean proofs of invertibility at the byte layer.

Lean module name:
  `IndisputableMonolith.Verification.MeaningCompiler.TextCodec`
-/

namespace IndisputableMonolith
namespace Verification
namespace MeaningCompiler

open Token

/-! ## Base types -/

/-- A byte value (0..255) as `Fin 256`. -/
abbrev Byte : Type := Fin 256

/-- A base-20 digit (0..19). -/
abbrev Digit20 : Type := Fin 20

/-! ## Digit ↔ WTokenId (canonical index) -/

/-- Convert a base-20 digit into the corresponding `WTokenId` by index. -/
def digitToWToken : Digit20 → WTokenId
  | ⟨0, _⟩  => .W0_Origin
  | ⟨1, _⟩  => .W1_Emergence
  | ⟨2, _⟩  => .W2_Polarity
  | ⟨3, _⟩  => .W3_Harmony
  | ⟨4, _⟩  => .W4_Power
  | ⟨5, _⟩  => .W5_Birth
  | ⟨6, _⟩  => .W6_Structure
  | ⟨7, _⟩  => .W7_Resonance
  | ⟨8, _⟩  => .W8_Infinity
  | ⟨9, _⟩  => .W9_Truth
  | ⟨10, _⟩ => .W10_Completion
  | ⟨11, _⟩ => .W11_Inspire
  | ⟨12, _⟩ => .W12_Transform
  | ⟨13, _⟩ => .W13_End
  | ⟨14, _⟩ => .W14_Connection
  | ⟨15, _⟩ => .W15_Wisdom
  | ⟨16, _⟩ => .W16_Illusion
  | ⟨17, _⟩ => .W17_Chaos
  | ⟨18, _⟩ => .W18_Twist
  | ⟨19, _⟩ => .W19_Time
  | _        => .W0_Origin  -- unreachable for `Fin 20`, but keeps the definition total

/-- Convert a `WTokenId` to its base-20 digit (0..19) via `toNat`. -/
def wtokenToDigit (w : WTokenId) : Digit20 :=
  ⟨WTokenId.toNat w, by
    cases w <;> decide⟩

@[simp] theorem digitToWToken_wtokenToDigit (w : WTokenId) :
    digitToWToken (wtokenToDigit w) = w := by
  cases w <;> rfl

@[simp] theorem wtokenToDigit_digitToWToken (d : Digit20) :
    wtokenToDigit (digitToWToken d) = d := by
  classical
  fin_cases d <;> rfl

/-! ## Byte ↔ (Digit20 × Digit20) -/

/-- Encode a byte as two base-20 digits (high, low). -/
def encodeByteDigits (b : Byte) : Digit20 × Digit20 :=
  let n : Nat := b.val
  have h_hi : n / 20 < 20 := by
    have h_lt : n < 20 * 20 := lt_trans b.isLt (by decide)
    exact Nat.div_lt_of_lt_mul h_lt
  let hi : Digit20 := ⟨n / 20, h_hi⟩
  let lo : Digit20 := ⟨n % 20, Nat.mod_lt _ (by decide : 0 < 20)⟩
  (hi, lo)

/-- Decode two base-20 digits into a byte, if the pair is in-range (0..255). -/
def decodeByteDigits? (hi lo : Digit20) : Option Byte :=
  let n : Nat := 20 * hi.val + lo.val
  if h : n < 256 then
    some ⟨n, h⟩
  else
    none

@[simp] theorem decode_encode_byteDigits (b : Byte) :
    decodeByteDigits? (encodeByteDigits b).1 (encodeByteDigits b).2 = some b := by
  classical
  unfold encodeByteDigits decodeByteDigits?

  have h_recon : 20 * (b.val / 20) + (b.val % 20) = b.val := by
    simpa using (Nat.div_add_mod b.val 20)

  have h_lt : 20 * (b.val / 20) + (b.val % 20) < 256 := by
    simpa [h_recon] using b.isLt

  have hb : (⟨20 * (b.val / 20) + (b.val % 20), h_lt⟩ : Byte) = b := by
    apply Fin.ext
    simpa [h_recon]

  simp [h_lt]
  have hproof :
      (⟨20 * (b.val / 20) + (b.val % 20), h_lt⟩ : Byte) =
        ⟨20 * (b.val / 20) + (b.val % 20), by simpa using h_lt⟩ := by
    apply Fin.ext
    rfl
  simpa [hproof] using hb

/-! ## Byte-list ↔ WTokenId stream -/

/-- Encode a byte as **two** `WTokenId`s (base-20 digits). -/
def encodeByte (b : Byte) : List WTokenId :=
  let (hi, lo) := encodeByteDigits b
  [digitToWToken hi, digitToWToken lo]

/-- Decode a pair of `WTokenId`s into a byte, failing if out-of-range. -/
def decodeByte? (w0 w1 : WTokenId) : Option Byte :=
  decodeByteDigits? (wtokenToDigit w0) (wtokenToDigit w1)

@[simp] theorem decode_encode_byte (b : Byte) :
    decodeByte?
        (digitToWToken (encodeByteDigits b).1)
        (digitToWToken (encodeByteDigits b).2)
      = some b := by
  simp [decodeByte?, decode_encode_byteDigits]

/-- Encode a list of bytes to a `WTokenId` stream (2 tokens per byte). -/
def encodeBytes (bs : List Byte) : List WTokenId :=
  bs.flatMap encodeByte

/-- Decode a `WTokenId` stream into bytes, requiring an even-length list and valid pairs. -/
def decodeBytes? : List WTokenId → Option (List Byte)
  | [] => some []
  | w0 :: w1 :: rest => do
      let b ← decodeByte? w0 w1
      let tail ← decodeBytes? rest
      return b :: tail
  | [_] => none

theorem decode_encode_bytes (bs : List Byte) :
    decodeBytes? (encodeBytes bs) = some bs := by
  induction bs with
  | nil =>
      simp [encodeBytes, decodeBytes?]
  | cons b tl ih =>
      have ih' : decodeBytes? (List.flatMap encodeByte tl) = some tl := by
        simpa [encodeBytes] using ih
      simp [encodeBytes, decodeBytes?, encodeByte, decode_encode_byte, ih']

end MeaningCompiler
end Verification
end IndisputableMonolith
