import Mathlib
import IndisputableMonolith.Water.WTokenIso

/-!
# Canonical WToken identity (`WTokenId`)

This module introduces a **single canonical identity** for the 20 semantic atoms (“WTokens”)
as used across:

- Water / amino-acid bridge (`IndisputableMonolith.Water.WTokenSpec`)
- LightLanguage / ULQ / other layers (future equivalences)

Claim hygiene:
- `WTokenId` is an **identifier type** (20 constructors).
- `toSpec`/`ofSpec` and `equivSpec` are **structural** (no empirical meaning claims).
- The mapping is intended to make “which token?” unambiguous across the repo.
-/

namespace IndisputableMonolith
namespace Token

open IndisputableMonolith.Water

/-- Canonical identity for the 20 semantic atoms (“WTokens”). -/
inductive WTokenId : Type
  | W0_Origin
  | W1_Emergence
  | W2_Polarity
  | W3_Harmony
  | W4_Power
  | W5_Birth
  | W6_Structure
  | W7_Resonance
  | W8_Infinity
  | W9_Truth
  | W10_Completion
  | W11_Inspire
  | W12_Transform
  | W13_End
  | W14_Connection
  | W15_Wisdom
  | W16_Illusion
  | W17_Chaos
  | W18_Twist
  | W19_Time
  deriving DecidableEq, Repr, Fintype

namespace WTokenId

/-- Numeric index (0..19). Useful for tables, serialization, and UI. -/
def toNat : WTokenId → Nat
  | W0_Origin => 0
  | W1_Emergence => 1
  | W2_Polarity => 2
  | W3_Harmony => 3
  | W4_Power => 4
  | W5_Birth => 5
  | W6_Structure => 6
  | W7_Resonance => 7
  | W8_Infinity => 8
  | W9_Truth => 9
  | W10_Completion => 10
  | W11_Inspire => 11
  | W12_Transform => 12
  | W13_End => 13
  | W14_Connection => 14
  | W15_Wisdom => 15
  | W16_Illusion => 16
  | W17_Chaos => 17
  | W18_Twist => 18
  | W19_Time => 19

/-- Human label (glossary entry). -/
def label : WTokenId → String
  | W0_Origin => "Origin"
  | W1_Emergence => "Emergence"
  | W2_Polarity => "Polarity"
  | W3_Harmony => "Harmony"
  | W4_Power => "Power"
  | W5_Birth => "Birth"
  | W6_Structure => "Structure"
  | W7_Resonance => "Resonance"
  | W8_Infinity => "Infinity"
  | W9_Truth => "Truth"
  | W10_Completion => "Completion"
  | W11_Inspire => "Inspire"
  | W12_Transform => "Transform"
  | W13_End => "End"
  | W14_Connection => "Connection"
  | W15_Wisdom => "Wisdom"
  | W16_Illusion => "Illusion"
  | W17_Chaos => "Chaos"
  | W18_Twist => "Twist"
  | W19_Time => "Time"

/-- Stable combined label, e.g. `W6 Structure`. -/
def fullLabel (w : WTokenId) : String :=
  "W" ++ toString w.toNat ++ " " ++ w.label

@[simp] theorem card_eq_20 : Fintype.card WTokenId = 20 := by native_decide

/-! ## Link to the existing canonical spec (`Water.WTokenSpec`) -/

/-- Canonical mapping: `WTokenId → Water.WTokenSpec` (the Water namespace spec). -/
def toSpec : WTokenId → Water.WTokenSpec
  | W0_Origin => Water.W0_Origin
  | W1_Emergence => Water.W1_Emergence
  | W2_Polarity => Water.W2_Polarity
  | W3_Harmony => Water.W3_Harmony
  | W4_Power => Water.W4_Power
  | W5_Birth => Water.W5_Birth
  | W6_Structure => Water.W6_Structure
  | W7_Resonance => Water.W7_Resonance
  | W8_Infinity => Water.W8_Infinity
  | W9_Truth => Water.W9_Truth
  | W10_Completion => Water.W10_Completion
  | W11_Inspire => Water.W11_Inspire
  | W12_Transform => Water.W12_Transform
  | W13_End => Water.W13_End
  | W14_Connection => Water.W14_Connection
  | W15_Wisdom => Water.W15_Wisdom
  | W16_Illusion => Water.W16_Illusion
  | W17_Chaos => Water.W17_Chaos
  | W18_Twist => Water.W18_Twist
  | W19_Time => Water.W19_Time

/-- Inverse mapping by structural fields. -/
def ofSpec : Water.WTokenSpec → WTokenId
  | ⟨.mode1_7, .level0, _, _⟩ => W0_Origin
  | ⟨.mode1_7, .level1, _, _⟩ => W1_Emergence
  | ⟨.mode1_7, .level2, _, _⟩ => W2_Polarity
  | ⟨.mode1_7, .level3, _, _⟩ => W3_Harmony

  | ⟨.mode2_6, .level0, _, _⟩ => W4_Power
  | ⟨.mode2_6, .level1, _, _⟩ => W5_Birth
  | ⟨.mode2_6, .level2, _, _⟩ => W6_Structure
  | ⟨.mode2_6, .level3, _, _⟩ => W7_Resonance

  | ⟨.mode3_5, .level0, _, _⟩ => W8_Infinity
  | ⟨.mode3_5, .level1, _, _⟩ => W9_Truth
  | ⟨.mode3_5, .level2, _, _⟩ => W10_Completion
  | ⟨.mode3_5, .level3, _, _⟩ => W11_Inspire

  | ⟨.mode4, .level0, .tau0, _⟩ => W12_Transform
  | ⟨.mode4, .level1, .tau0, _⟩ => W13_End
  | ⟨.mode4, .level2, .tau0, _⟩ => W14_Connection
  | ⟨.mode4, .level3, .tau0, _⟩ => W15_Wisdom

  | ⟨.mode4, .level0, .tau2, _⟩ => W16_Illusion
  | ⟨.mode4, .level1, .tau2, _⟩ => W17_Chaos
  | ⟨.mode4, .level2, .tau2, _⟩ => W18_Twist
  | ⟨.mode4, .level3, .tau2, _⟩ => W19_Time

@[simp] theorem ofSpec_toSpec (w : WTokenId) : ofSpec (toSpec w) = w := by
  cases w <;> rfl

/-- Proof-irrelevance helper for `Water.WTokenSpec` (its proof field lives in `Prop`). -/
private theorem mk_eq : ∀ (m : WTokenMode) (p : PhiLevel) (t : TauOffset)
    (h₁ h₂ : m ≠ WTokenMode.mode4 → t = TauOffset.tau0),
    (⟨m, p, t, h₁⟩ : Water.WTokenSpec) = ⟨m, p, t, h₂⟩ := by
  intro m p t h₁ h₂
  have : h₁ = h₂ := by
    apply Subsingleton.elim
  cases this
  rfl

@[simp] theorem toSpec_ofSpec (w : Water.WTokenSpec) : toSpec (ofSpec w) = w := by
  cases w with
  | mk mode phi tau hv =>
    cases mode with
    | mode1_7 =>
        have ht : tau = TauOffset.tau0 := hv (by decide)
        cases ht
        cases phi <;>
          simp [toSpec, ofSpec,
            Water.W0_Origin, Water.W1_Emergence, Water.W2_Polarity, Water.W3_Harmony]
    | mode2_6 =>
        have ht : tau = TauOffset.tau0 := hv (by decide)
        cases ht
        cases phi <;>
          simp [toSpec, ofSpec,
            Water.W4_Power, Water.W5_Birth, Water.W6_Structure, Water.W7_Resonance]
    | mode3_5 =>
        have ht : tau = TauOffset.tau0 := hv (by decide)
        cases ht
        cases phi <;>
          simp [toSpec, ofSpec,
            Water.W8_Infinity, Water.W9_Truth, Water.W10_Completion, Water.W11_Inspire]
    | mode4 =>
        cases phi <;> cases tau <;>
          simp [toSpec, ofSpec,
            Water.W12_Transform, Water.W13_End, Water.W14_Connection, Water.W15_Wisdom,
            Water.W16_Illusion, Water.W17_Chaos, Water.W18_Twist, Water.W19_Time]

/-- Packaged equivalence: canonical IDs are exactly the Water spec tokens. -/
def equivSpec : WTokenId ≃ Water.WTokenSpec :=
{ toFun := toSpec
, invFun := ofSpec
, left_inv := by intro w; simp [ofSpec_toSpec]
, right_inv := by intro s; simp [toSpec_ofSpec]
}

end WTokenId

end Token
end IndisputableMonolith
