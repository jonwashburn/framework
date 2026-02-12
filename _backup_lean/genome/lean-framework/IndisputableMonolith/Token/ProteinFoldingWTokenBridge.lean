import Mathlib
import IndisputableMonolith.Token.WTokenId
import IndisputableMonolith.ProteinFolding.Encoding.WToken

/-!
# Bridge: ProteinFolding per-position `WToken` → canonical `Token.WTokenId` (MODEL)

`IndisputableMonolith.ProteinFolding.Encoding.WToken` defines a per-residue recognition signature:

- `dominantMode : Fin 8` (DFT mode index)
- `phiLevel : Fin 4` (φ-ladder level)
- `phase : Fin 8` (local phase bin)

This is not definitionally the same object as the repo’s canonical 20 semantic atoms
(`Token.WTokenId`). In particular:

- ProteinFolding’s `phase : Fin 8` is a *local* phase bin for a residue,
  while the Water/ULL token family uses `tau_offset` only in the special mode-4
  real/imag split (τ ∈ {0,2}).

Therefore this bridge is a **MODEL projection**:

- We map `dominantMode` to one of the four ULL mode families {1/7, 2/6, 3/5, 4}.
- We map `phiLevel` directly to the corresponding within-family index (0..3).
- For the mode-4 family, we *coarsely* classify the local phase bin as “near real axis”
  vs “near imaginary axis” to choose between τ-offset 0 vs 2.

This reduces ambiguity in cross-module discussions (“which WToken do you mean?”),
but it should not be interpreted as a derived/forced chemical mapping.
-/

namespace IndisputableMonolith
namespace Token

open IndisputableMonolith.ProteinFolding

namespace ProteinFoldingWTokenBridge

abbrev PFToken := IndisputableMonolith.ProteinFolding.WToken.WToken

/-- Map a DFT mode index to the ULL “mode family” (if non-DC). -/
def familyOfDominantMode? (k : Fin 8) : Option Nat :=
  -- We use representative families by value:
  -- 1/7 → family 1, 2/6 → family 2, 3/5 → family 3, 4 → family 4.
  match k.val with
  | 1 | 7 => some 1
  | 2 | 6 => some 2
  | 3 | 5 => some 3
  | 4     => some 4
  | _     => none

/-- For mode-4 only: classify a local phase bin as “near real axis” vs “near imaginary axis”.

Heuristic (8 bins of width π/4):
- near real axis: indices {0,3,4,7}
- near imag axis: indices {1,2,5,6}

This is a coarse projection used only to pick between the mode-4 τ-offset variants. -/
def mode4TauOffsetOfPhase (τ : Fin 8) : Bool :=
  match τ.val with
  | 0 | 3 | 4 | 7 => true   -- “real-like”
  | _             => false  -- “imag-like”

/-- Project a ProteinFolding per-position token to a canonical semantic ID (when possible). -/
def toWTokenId? (w : PFToken) : Option Token.WTokenId :=
  match familyOfDominantMode? w.dominantMode with
  | none => none
  | some fam =>
      -- phiLevel is already Fin 4; use its `.val` (0..3) to pick the within-family id.
      match fam, w.phiLevel.val with
      | 1, 0 => some .W0_Origin
      | 1, 1 => some .W1_Emergence
      | 1, 2 => some .W2_Polarity
      | 1, 3 => some .W3_Harmony

      | 2, 0 => some .W4_Power
      | 2, 1 => some .W5_Birth
      | 2, 2 => some .W6_Structure
      | 2, 3 => some .W7_Resonance

      | 3, 0 => some .W8_Infinity
      | 3, 1 => some .W9_Truth
      | 3, 2 => some .W10_Completion
      | 3, 3 => some .W11_Inspire

      | 4, 0 =>
          if mode4TauOffsetOfPhase w.phase then some .W12_Transform else some .W16_Illusion
      | 4, 1 =>
          if mode4TauOffsetOfPhase w.phase then some .W13_End else some .W17_Chaos
      | 4, 2 =>
          if mode4TauOffsetOfPhase w.phase then some .W14_Connection else some .W18_Twist
      | 4, 3 =>
          if mode4TauOffsetOfPhase w.phase then some .W15_Wisdom else some .W19_Time

      | _, _ => none

end ProteinFoldingWTokenBridge

end Token
end IndisputableMonolith
