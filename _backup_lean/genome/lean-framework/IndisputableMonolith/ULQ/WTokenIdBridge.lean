import Mathlib
import IndisputableMonolith.Token.WTokenLightLanguageBridge
import IndisputableMonolith.ULQ.Core

/-!
# ULQ ↔ canonical token identity bridge

This module connects the **canonical semantic identity** `Token.WTokenId` to the ULQ layer.

Operational intent (WS3.2):
- ULQ’s core maps are defined on `LightLanguage.WToken`.
- The repo now has a canonical identity `Token.WTokenId` (20 constructors) with
  equivalence to `Water.WTokenSpec`.
- Here we provide a **single, explicit path**:

`WTokenId → LightLanguage.WToken → QualiaSpace / QToken`

Claim hygiene:
- The embedding `WTokenId → LightLanguage.WToken` is marked MODEL in
  `Token/WTokenLightLanguageBridge.lean`.
- This file does not claim the ULQ derivation is “forced by reality”;
  it only provides the formally well-typed connection surface.
-/

namespace IndisputableMonolith
namespace ULQ

open IndisputableMonolith.Token
open LightLanguage

/-- Canonical embedding of a `WTokenId` as a `LightLanguage.WToken` (MODEL). -/
noncomputable def wtokenOfId (id : Token.WTokenId) : LightLanguage.WToken :=
  Token.WTokenId.toLightLanguageWToken id

/-- The ULQ qualia space associated with a canonical token id. -/
noncomputable def qualiaOfId (id : Token.WTokenId) : QualiaSpace :=
  let w := wtokenOfId id
  { mode := qualiaModeOfWToken w
  , intensity := deriveIntensity w
  , valence := deriveValence w
  , temporal := deriveTemporalQuality w
  }

/-- A QToken associated with a canonical token id (with chosen definiteness). -/
noncomputable def qtokenOfId (id : Token.WTokenId) (isDefinite : Bool) : QToken :=
  let w := wtokenOfId id
  let q := qualiaOfId id
  { wtoken := w
  , qualia := q
  , definite := isDefinite
  , coherent := rfl
  }

@[simp] theorem qtokenOfId_coherent (id : Token.WTokenId) (isDefinite : Bool) :
    (qtokenOfId id isDefinite).qualia.mode = qualiaModeOfWToken (qtokenOfId id isDefinite).wtoken := by
  rfl

end ULQ
end IndisputableMonolith
