import Mathlib
import IndisputableMonolith.Token.WTokenBasis
import IndisputableMonolith.LightLanguage.Core

/-!
# Bridge: `Token.WTokenId` → `LightLanguage.WToken` (MODEL)

This module provides a **canonical injection** from the repo-wide identity `Token.WTokenId`
into the existing `LightLanguage.WToken` record.

Claim hygiene:
- This is a **MODEL embedding** of IDs into a richer token record.
- The important part is **not** the auxiliary metadata fields (`nu_phi`, `ell`, `k_perp`, …),
  which are currently chosen conservatively.
- The important part *is* that the produced token’s `basis` is constructed from DFT8 and
  the required `neutral` / `normalized` proofs are **derived** (not assumed as data).
-/

namespace IndisputableMonolith
namespace Token

open IndisputableMonolith.Water
open IndisputableMonolith.LightLanguage

namespace WTokenId

/-- Map Water φ-level to a small natural index (0..3). -/
def phiLevelIndex : Water.PhiLevel → Nat
  | .level0 => 0
  | .level1 => 1
  | .level2 => 2
  | .level3 => 3

/-- Map Water τ-offset to an 8-tick index used by the LightLanguage token record. -/
def tauOffsetToFin : Water.TauOffset → Fin LightLanguage.tauZero
  | .tau0 => ⟨0, by decide⟩
  | .tau2 => ⟨2, by decide⟩

/-- MODEL: embed a `WTokenId` as a `LightLanguage.WToken`.

Notes:
- `basis` is the DFT8-backed construction from `Token.WTokenId.basisOfId`.
- `neutral` and `normalized` are proved from DFT8 facts (no proof-fields-as-data).
- Other fields are conservative placeholders until the “forced” story is mechanized.
-/
noncomputable def toLightLanguageWToken (w : Token.WTokenId) : LightLanguage.WToken :=
  let spec := WTokenId.toSpec w
  { nu_phi := (dftModeOfFamily spec.mode).val * (LightLanguage.phi ^ (phiLevelIndex spec.phi_level : ℝ))
  , ell := 1
  , sigma := 0
  , tau := tauOffsetToFin spec.tau_offset
  , k_perp := (0, 0, 0)
  , phi_e := 0
  , basis := basisOfId w
  , neutral := by
      -- `basisOfId_neutral` is stated over `Fin 8`; `tauZero` is definitionally 8.
      simpa [LightLanguage.tauZero] using basisOfId_neutral w
  , normalized := by
      simpa [LightLanguage.tauZero] using basisOfId_normalized w
  }

@[simp] theorem toLightLanguageWToken_basis (w : Token.WTokenId) :
    (toLightLanguageWToken w).basis = basisOfId w := rfl

end WTokenId

end Token
end IndisputableMonolith
