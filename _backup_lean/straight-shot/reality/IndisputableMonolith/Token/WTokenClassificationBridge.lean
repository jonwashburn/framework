import Mathlib
import IndisputableMonolith.Token.WTokenId
import IndisputableMonolith.LightLanguage.WTokenClassification

/-!
# Bridge: `LightLanguage.WTokenClassification.WTokenSpec` ↔ canonical `Token.WTokenId`

The repo historically had multiple incompatible “WToken spec” notions. This module makes the
relationship between:

- `IndisputableMonolith.LightLanguage.WTokenClassification.WTokenSpec` (classification spec), and
- `IndisputableMonolith.Token.WTokenId` (canonical identity, 20 constructors)

**explicit**.

Claim hygiene:
- This bridge is about *identity / bookkeeping* (which token is meant), not about “forcing.”
- The mapping is intentionally conservative: it recognizes only the canonical 20 patterns
  used in the classification story (modes 1/2/3 + mode4 real/imag; φ-level 0..3; τ-offset 0 or 2).
- Anything outside that canonical surface maps to `none`.
-/

namespace IndisputableMonolith
namespace Token

open IndisputableMonolith.LightLanguage

namespace WTokenClassificationBridge

open LightLanguage.WTokenClassification

/-- The canonical `WTokenClassification.WTokenSpec` corresponding to a `Token.WTokenId`. -/
def specOfId : Token.WTokenId → LightLanguage.WTokenClassification.WTokenSpec
  | .W0_Origin      => ⟨⟨1, by decide⟩, true, 0, ⟨0, by decide⟩⟩
  | .W1_Emergence   => ⟨⟨1, by decide⟩, true, 1, ⟨0, by decide⟩⟩
  | .W2_Polarity    => ⟨⟨1, by decide⟩, true, 2, ⟨0, by decide⟩⟩
  | .W3_Harmony     => ⟨⟨1, by decide⟩, true, 3, ⟨0, by decide⟩⟩

  | .W4_Power       => ⟨⟨2, by decide⟩, true, 0, ⟨0, by decide⟩⟩
  | .W5_Birth       => ⟨⟨2, by decide⟩, true, 1, ⟨0, by decide⟩⟩
  | .W6_Structure   => ⟨⟨2, by decide⟩, true, 2, ⟨0, by decide⟩⟩
  | .W7_Resonance   => ⟨⟨2, by decide⟩, true, 3, ⟨0, by decide⟩⟩

  | .W8_Infinity    => ⟨⟨3, by decide⟩, true, 0, ⟨0, by decide⟩⟩
  | .W9_Truth       => ⟨⟨3, by decide⟩, true, 1, ⟨0, by decide⟩⟩
  | .W10_Completion => ⟨⟨3, by decide⟩, true, 2, ⟨0, by decide⟩⟩
  | .W11_Inspire    => ⟨⟨3, by decide⟩, true, 3, ⟨0, by decide⟩⟩

  -- Mode 4 “real” (τ-offset 0)
  | .W12_Transform  => ⟨⟨4, by decide⟩, false, 0, ⟨0, by decide⟩⟩
  | .W13_End        => ⟨⟨4, by decide⟩, false, 1, ⟨0, by decide⟩⟩
  | .W14_Connection => ⟨⟨4, by decide⟩, false, 2, ⟨0, by decide⟩⟩
  | .W15_Wisdom     => ⟨⟨4, by decide⟩, false, 3, ⟨0, by decide⟩⟩

  -- Mode 4 “imag” (τ-offset 2)
  | .W16_Illusion   => ⟨⟨4, by decide⟩, false, 0, ⟨2, by decide⟩⟩
  | .W17_Chaos      => ⟨⟨4, by decide⟩, false, 1, ⟨2, by decide⟩⟩
  | .W18_Twist      => ⟨⟨4, by decide⟩, false, 2, ⟨2, by decide⟩⟩
  | .W19_Time       => ⟨⟨4, by decide⟩, false, 3, ⟨2, by decide⟩⟩

/-- Partial parser: recognize a canonical `Token.WTokenId` from a classification spec. -/
def idOfSpec? (s : LightLanguage.WTokenClassification.WTokenSpec) : Option Token.WTokenId :=
  match s.primary_mode.val with
  | 1 =>
      if s.is_conjugate_pair then
        if _hτ : s.tau_offset.val = 0 then
          match s.phi_level with
          | 0 => some .W0_Origin
          | 1 => some .W1_Emergence
          | 2 => some .W2_Polarity
          | 3 => some .W3_Harmony
          | _ => none
        else none
      else none
  | 2 =>
      if s.is_conjugate_pair then
        if _hτ : s.tau_offset.val = 0 then
          match s.phi_level with
          | 0 => some .W4_Power
          | 1 => some .W5_Birth
          | 2 => some .W6_Structure
          | 3 => some .W7_Resonance
          | _ => none
        else none
      else none
  | 3 =>
      if s.is_conjugate_pair then
        if _hτ : s.tau_offset.val = 0 then
          match s.phi_level with
          | 0 => some .W8_Infinity
          | 1 => some .W9_Truth
          | 2 => some .W10_Completion
          | 3 => some .W11_Inspire
          | _ => none
        else none
      else none
  | 4 =>
      if s.is_conjugate_pair then
        none
      else
        match s.tau_offset.val with
        | 0 =>
            match s.phi_level with
            | 0 => some .W12_Transform
            | 1 => some .W13_End
            | 2 => some .W14_Connection
            | 3 => some .W15_Wisdom
            | _ => none
        | 2 =>
            match s.phi_level with
            | 0 => some .W16_Illusion
            | 1 => some .W17_Chaos
            | 2 => some .W18_Twist
            | 3 => some .W19_Time
            | _ => none
        | _ => none
  | _ => none

@[simp] theorem idOfSpec?_specOfId (id : Token.WTokenId) :
    idOfSpec? (specOfId id) = some id := by
  cases id <;> rfl

end WTokenClassificationBridge

end Token
end IndisputableMonolith
