import Mathlib
import IndisputableMonolith.Verification.MeaningCompiler.TextCodec

/-!
# Text → (byte-signal) → WTokenId stream (Certified IO Pipeline)

This module wires **Lean core UTF-8** to the certified byte↔WToken codec:

  `String` → UTF-8 bytes → `List Byte` (our signal) → `List WTokenId`

Notes:
- The *certified* portion is the byte-layer codec (`TextCodec.lean`).
- `String.toUTF8` / `String.fromUTF8?` are Lean core primitives; we treat them as the
  trusted acquisition boundary.
- This is still an acquisition codec, not a semantic decomposition algorithm.
-/

namespace IndisputableMonolith
namespace Verification
namespace MeaningCompiler

open Token

/-! ## UTF-8 ByteArray ↔ `List Byte` -/

/-- Convert a `UInt8` to a `Byte` (`Fin 256`). -/
def uint8ToByte (u : UInt8) : Byte :=
  ⟨u.toNat, by
    -- `UInt8.toNat_lt u : u.toNat < 2^8`, and `2^8 = 256`.
    simpa using (UInt8.toNat_lt u)⟩

/-- Convert a `Byte` (`Fin 256`) to a `UInt8`. -/
def byteToUInt8 (b : Byte) : UInt8 :=
  UInt8.ofNat b.val

/-- Interpret a `String` as a byte-signal (UTF-8 bytes). -/
def textToSignal (s : String) : List Byte :=
  s.toUTF8.toList.map uint8ToByte

/-- Attempt to decode a byte-signal (UTF-8 bytes) back into a `String`. -/
def signalToText? (bs : List Byte) : Option String :=
  let arr : Array UInt8 := (bs.map byteToUInt8).toArray
  String.fromUTF8? (ByteArray.mk arr)

/-! ## Text ↔ WTokenId stream -/

/-- Encode text to a WTokenId stream via the certified byte-layer codec. -/
def encodeText (s : String) : List WTokenId :=
  encodeBytes (textToSignal s)

/-- Decode a WTokenId stream back into text (if the bytes form valid UTF-8). -/
def decodeText? (ws : List WTokenId) : Option String :=
  match decodeBytes? ws with
  | none => none
  | some bs => signalToText? bs

theorem decode_encode_text_signal (s : String) :
    decodeBytes? (encodeText s) = some (textToSignal s) := by
  simp [encodeText, textToSignal, decode_encode_bytes]

end MeaningCompiler
end Verification
end IndisputableMonolith
