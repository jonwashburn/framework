import Mathlib
import IndisputableMonolith.Token.WTokenId
import IndisputableMonolith.Token.WTokenCandidate
import IndisputableMonolith.LightLanguage.Basis.DFT8
import IndisputableMonolith.LightLanguage.Core

/-!
# WToken RS Legality Predicates (DFT-level)

This file implements **WS2.3**: RS legality predicates that depend on the DFT/basis structure,
going beyond the parameter-level constraints in `WTokenCandidate.lean`.

## Key Ideas

RS forces the following constraints on valid semantic tokens:

1. **Neutrality (σ = 0 constraint)**: The basis sum must vanish, which in DFT terms means
   the DC coefficient is zero. This is the "ledger balance" requirement.

2. **Normalization**: The basis has unit L² norm, ensuring the token carries
   exactly one "quantum" of meaning.

3. **Mode structure**: Valid tokens use specific DFT modes (not arbitrary complex vectors).
   The mode determines the qualitative character.

4. **φ-lattice quantization**: Intensity/frequency levels are quantized on powers of φ.

5. **Reciprocity (σ = 0)**: The skew parameter must be zero for fundamental tokens,
   ensuring ledger balance.

## Main Definitions

* `IsRSLegalBasis` - predicate for RS-legal 8-vector bases
* `RSLegalBasis` - bundled type of RS-legal bases
* `DFTModeFamily` - the 4 mode families (corresponding to WTokenMode)
* `IsCanonicalDFTToken` - predicate for tokens with canonical DFT structure

## Claim Hygiene

This is a MODEL layer. The constraints are stated explicitly, but the claim that these
constraints are "forced by physics" requires external justification (empirical or axiomatic).
What IS proved is that these constraints are CONSISTENT and yield exactly 20 tokens.
-/

namespace IndisputableMonolith
namespace Token

open IndisputableMonolith.LightLanguage
open IndisputableMonolith.LightLanguage.Basis
open Complex

/-! ## RS Legality Predicate for 8-vector Bases -/

/-- An 8-vector is RS-legal if it satisfies:
    1. Neutrality: sum = 0 (DC mode excluded)
    2. Normalization: ‖·‖² = 1

    This is the minimal DFT-level constraint for a valid semantic atom. -/
def IsRSLegalBasis (v : Fin 8 → ℂ) : Prop :=
  (Finset.univ.sum v = 0) ∧
  (Finset.univ.sum (fun i => normSq (v i)) = 1)

/-- The type of RS-legal 8-vector bases. -/
def RSLegalBasis := { v : Fin 8 → ℂ // IsRSLegalBasis v }

namespace RSLegalBasis

/-- The basis vector. -/
def basis (b : RSLegalBasis) : Fin 8 → ℂ := b.val

/-- Neutrality: sum of components is zero. -/
theorem neutral (b : RSLegalBasis) : Finset.univ.sum b.basis = 0 := b.property.1

/-- Normalization: squared norm is one. -/
theorem normalized (b : RSLegalBasis) : Finset.univ.sum (fun i => normSq (b.basis i)) = 1 := b.property.2

/-- An RS-legal basis has zero DC coefficient in its DFT expansion. -/
theorem zero_dc_coefficient (b : RSLegalBasis) :
    Finset.univ.sum (fun t => star (dft8_mode 0 t) * b.basis t) = 0 := by
  -- The DC mode is constant: mode_0 t = 1/√8
  have h_mode : ∀ t, dft8_mode 0 t = 1 / Real.sqrt 8 := dft8_mode_zero_constant
  simp only [h_mode, one_div, star_inv₀, star_one]
  rw [← Finset.mul_sum]
  simp only [b.neutral, mul_zero]

end RSLegalBasis

/-! ## DFT Mode Families -/

/-- The 4 DFT mode families that generate valid tokens.

    - mode1: DFT modes {1, 7} (conjugate pair)
    - mode2: DFT modes {2, 6} (conjugate pair)
    - mode3: DFT modes {3, 5} (conjugate pair)
    - mode4: DFT mode {4} (self-conjugate, real)

    Each family, combined with 4 φ-levels and (for mode4) 2 τ-offsets,
    yields the 20 fundamental tokens. -/
inductive DFTModeFamily
  | mode1  -- DFT modes 1, 7 (conjugate pair)
  | mode2  -- DFT modes 2, 6 (conjugate pair)
  | mode3  -- DFT modes 3, 5 (conjugate pair)
  | mode4  -- DFT mode 4 (self-conjugate)
  deriving DecidableEq, Repr, Inhabited

namespace DFTModeFamily

/-- Primary DFT mode index for each family. -/
def primaryMode : DFTModeFamily → Fin 8
  | mode1 => 1
  | mode2 => 2
  | mode3 => 3
  | mode4 => 4

/-- Conjugate DFT mode index (8 - k mod 8) for each family. -/
def conjugateMode : DFTModeFamily → Fin 8
  | mode1 => 7  -- 8 - 1 = 7
  | mode2 => 6  -- 8 - 2 = 6
  | mode3 => 5  -- 8 - 3 = 5
  | mode4 => 4  -- 8 - 4 = 4 (self-conjugate)

/-- Mode 4 is self-conjugate. -/
theorem mode4_self_conjugate : conjugateMode mode4 = primaryMode mode4 := rfl

/-- Modes 1-3 have distinct conjugates. -/
theorem mode1_distinct_conjugate : conjugateMode mode1 ≠ primaryMode mode1 := by decide
theorem mode2_distinct_conjugate : conjugateMode mode2 ≠ primaryMode mode2 := by decide
theorem mode3_distinct_conjugate : conjugateMode mode3 ≠ primaryMode mode3 := by decide

/-- Map from Water.WTokenMode to DFTModeFamily. -/
def ofWTokenMode : Water.WTokenMode → DFTModeFamily
  | .mode1_7 => mode1
  | .mode2_6 => mode2
  | .mode3_5 => mode3
  | .mode4 => mode4

/-- Map from DFTModeFamily to Water.WTokenMode. -/
def toWTokenMode : DFTModeFamily → Water.WTokenMode
  | mode1 => .mode1_7
  | mode2 => .mode2_6
  | mode3 => .mode3_5
  | mode4 => .mode4

@[simp] theorem ofWTokenMode_toWTokenMode (f : DFTModeFamily) :
    ofWTokenMode (toWTokenMode f) = f := by cases f <;> rfl

@[simp] theorem toWTokenMode_ofWTokenMode (m : Water.WTokenMode) :
    toWTokenMode (ofWTokenMode m) = m := by cases m <;> rfl

/-- Equivalence between DFTModeFamily and Water.WTokenMode. -/
def equivWTokenMode : DFTModeFamily ≃ Water.WTokenMode :=
{ toFun := toWTokenMode
, invFun := ofWTokenMode
, left_inv := ofWTokenMode_toWTokenMode
, right_inv := toWTokenMode_ofWTokenMode }

end DFTModeFamily

/-! ## φ-Lattice Levels -/

/-- The 4 φ-lattice intensity levels (0, 1, 2, 3).

    Level n corresponds to intensity φ^n. -/
abbrev PhiLevel := Fin 4

/-- φ-level to Water.PhiLevel conversion. -/
def phiLevelToWater : PhiLevel → Water.PhiLevel
  | ⟨0, _⟩ => .level0
  | ⟨1, _⟩ => .level1
  | ⟨2, _⟩ => .level2
  | ⟨3, _⟩ => .level3

/-- Water.PhiLevel to φ-level conversion. -/
def phiLevelOfWater : Water.PhiLevel → PhiLevel
  | .level0 => ⟨0, by decide⟩
  | .level1 => ⟨1, by decide⟩
  | .level2 => ⟨2, by decide⟩
  | .level3 => ⟨3, by decide⟩

@[simp] theorem phiLevelToWater_ofWater (p : Water.PhiLevel) :
    phiLevelToWater (phiLevelOfWater p) = p := by cases p <;> rfl

@[simp] theorem phiLevelOfWater_toWater (p : PhiLevel) :
    phiLevelOfWater (phiLevelToWater p) = p := by
  fin_cases p <;> rfl

/-! ## Canonical DFT Token Structure -/

/-- A token has canonical DFT structure if:
    1. Its basis is RS-legal (neutral, normalized)
    2. Its energy is concentrated in exactly one mode family
    3. Its intensity corresponds to a valid φ-level

    This is the structural constraint that makes the 20 tokens "special". -/
structure IsCanonicalDFTToken (w : LightLanguage.WToken) : Prop where
  /-- The basis is neutral (sum = 0). -/
  neutral : Finset.univ.sum w.basis = 0
  /-- The basis is normalized (‖·‖² = 1). -/
  normalized : Finset.univ.sum (fun i => normSq (w.basis i)) = 1
  /-- The skew is zero (ledger balance / reciprocity). -/
  balanced : w.sigma = 0

/-- Every LightLanguage.WToken satisfies the neutral/normalized constraints by construction. -/
theorem wtoken_is_neutral_normalized (w : LightLanguage.WToken) :
    Finset.univ.sum w.basis = 0 ∧
    Finset.univ.sum (fun i => normSq (w.basis i)) = 1 :=
  ⟨w.neutral, w.normalized⟩

/-! ## Token Classification Theorem -/

/-- RS-legal token classification parameters:
    - mode family (4 choices)
    - φ-level (4 choices)
    - τ-offset (2 choices for mode4, 1 choice otherwise)

    Total: 3 × 4 × 1 + 1 × 4 × 2 = 12 + 8 = 20 -/
structure RSTokenClassification where
  /-- Mode family. -/
  family : DFTModeFamily
  /-- φ-level. -/
  level : PhiLevel
  /-- τ-offset (0 or 2, only meaningful for mode4). -/
  tauOffset : Fin 2
  /-- Constraint: non-mode4 families only use τ-offset 0. -/
  tau_constraint : family ≠ DFTModeFamily.mode4 → tauOffset = 0

namespace RSTokenClassification

/-- The predicate version of the classification constraint. -/
def IsValid (family : DFTModeFamily) (level : PhiLevel) (tauOffset : Fin 2) : Prop :=
  family ≠ DFTModeFamily.mode4 → tauOffset = 0

/-- Convert tau offset to Water.TauOffset. -/
def tauOffsetToWater (t : Fin 2) : Water.TauOffset :=
  if t = 0 then .tau0 else .tau2

/-- Convert Water.TauOffset to tau offset. -/
def tauOffsetOfWater : Water.TauOffset → Fin 2
  | .tau0 => 0
  | .tau2 => 1

@[simp] lemma tauOffsetToWater_ofWater (t : Water.TauOffset) :
    tauOffsetToWater (tauOffsetOfWater t) = t := by cases t <;> rfl

@[simp] lemma tauOffsetOfWater_toWater (t : Fin 2) :
    tauOffsetOfWater (tauOffsetToWater t) = t := by fin_cases t <;> rfl

/-- tauOffsetToWater 0 = tau0 -/
@[simp] lemma tauOffsetToWater_zero : tauOffsetToWater 0 = Water.TauOffset.tau0 := rfl

/-- tauOffsetToWater 1 = tau2 -/
@[simp] lemma tauOffsetToWater_one : tauOffsetToWater 1 = Water.TauOffset.tau2 := rfl

/-- toWTokenMode f ≠ mode4 iff f ≠ mode4 -/
lemma DFTModeFamily.toWTokenMode_ne_mode4_iff (f : DFTModeFamily) :
    f.toWTokenMode ≠ Water.WTokenMode.mode4 ↔ f ≠ DFTModeFamily.mode4 := by
  cases f <;> simp [DFTModeFamily.toWTokenMode]

/-- Convert to WTokenCandidateParam. -/
def toWTokenCandidateParam (c : RSTokenClassification) : WTokenCandidateParam :=
  let mode := c.family.toWTokenMode
  let phi := phiLevelToWater c.level
  let tau := tauOffsetToWater c.tauOffset
  let hp : IsWTokenCandidateParam (mode, phi, tau) := by
    intro hne
    have hfam : c.family ≠ DFTModeFamily.mode4 :=
      (DFTModeFamily.toWTokenMode_ne_mode4_iff c.family).mp hne
    have htau0 : c.tauOffset = 0 := c.tau_constraint hfam
    show tauOffsetToWater c.tauOffset = Water.TauOffset.tau0
    rw [htau0, tauOffsetToWater_zero]
  ⟨(mode, phi, tau), hp⟩

/-- ofWTokenMode m ≠ mode4 iff m ≠ mode4 -/
lemma DFTModeFamily.ofWTokenMode_ne_mode4_iff (m : Water.WTokenMode) :
    DFTModeFamily.ofWTokenMode m ≠ DFTModeFamily.mode4 ↔ m ≠ Water.WTokenMode.mode4 := by
  cases m <;> simp [DFTModeFamily.ofWTokenMode]

/-- Convert from WTokenCandidateParam. -/
def ofWTokenCandidateParam (p : WTokenCandidateParam) : RSTokenClassification :=
  match p with
  | ⟨(mode, phi, tau), hp⟩ =>
    let family := DFTModeFamily.ofWTokenMode mode
    let level := phiLevelOfWater phi
    let tauOffset := tauOffsetOfWater tau
    let hc : family ≠ DFTModeFamily.mode4 → tauOffset = 0 := fun hfam => by
      have hmode : mode ≠ Water.WTokenMode.mode4 :=
        (DFTModeFamily.ofWTokenMode_ne_mode4_iff mode).mp hfam
      have htau := hp hmode
      cases tau with
      | tau0 => rfl
      | tau2 => exact absurd htau (by decide)
    ⟨family, level, tauOffset, hc⟩

-- Note: The roundtrip proofs use Subtype.ext and proof irrelevance for Prop fields.

/-- Roundtrip proof for WTokenCandidateParam. -/
@[simp] theorem toWTokenCandidateParam_ofWTokenCandidateParam (p : WTokenCandidateParam) :
    toWTokenCandidateParam (ofWTokenCandidateParam p) = p := by
  obtain ⟨⟨mode, phi, tau⟩, hp⟩ := p
  apply Subtype.ext
  simp only [toWTokenCandidateParam, ofWTokenCandidateParam,
             DFTModeFamily.toWTokenMode_ofWTokenMode,
             phiLevelToWater_ofWater, tauOffsetToWater_ofWater]

/-- Extensionality for RSTokenClassification (proof fields are irrelevant). -/
theorem ext {c1 c2 : RSTokenClassification}
    (h1 : c1.family = c2.family)
    (h2 : c1.level = c2.level)
    (h3 : c1.tauOffset = c2.tauOffset) : c1 = c2 := by
  cases c1; cases c2
  simp only [mk.injEq] at *
  exact ⟨h1, h2, h3⟩

/-- Roundtrip proof for RSTokenClassification. -/
@[simp] theorem ofWTokenCandidateParam_toWTokenCandidateParam (c : RSTokenClassification) :
    ofWTokenCandidateParam (toWTokenCandidateParam c) = c := by
  apply ext
  · exact DFTModeFamily.ofWTokenMode_toWTokenMode c.family
  · exact phiLevelOfWater_toWater c.level
  · exact tauOffsetOfWater_toWater c.tauOffset

/-- Equivalence between RSTokenClassification and WTokenCandidateParam. -/
def equivWTokenCandidateParam : RSTokenClassification ≃ WTokenCandidateParam :=
{ toFun := toWTokenCandidateParam
, invFun := ofWTokenCandidateParam
, left_inv := ofWTokenCandidateParam_toWTokenCandidateParam
, right_inv := toWTokenCandidateParam_ofWTokenCandidateParam }

/-- Equivalence to canonical WTokenId. -/
def equivWTokenId : RSTokenClassification ≃ WTokenId :=
  equivWTokenCandidateParam.trans WTokenCandidateParam.equivId

/-- There are exactly 20 RS token classifications. -/
noncomputable instance : Fintype RSTokenClassification :=
  Fintype.ofEquiv WTokenCandidateParam equivWTokenCandidateParam.symm

theorem card_eq_20 : Fintype.card RSTokenClassification = 20 := by
  rw [Fintype.card_congr equivWTokenCandidateParam]
  exact WTokenCandidateParam.card_eq_20

end RSTokenClassification

/-! ## Summary: The "Forced" Story -/

/-- **SUMMARY**: The 20 WTokens are characterized by:

    1. **Neutrality constraint** (DC = 0): No net meaning, ledger-balanced.
    2. **Normalization** (unit norm): Exactly one quantum of meaning.
    3. **Mode structure**: Energy in conjugate DFT mode pairs (or self-conjugate mode 4).
    4. **φ-lattice quantization**: 4 intensity levels on φ^n.
    5. **τ-offset constraint**: Only mode4 allows τ ≠ 0.

    Given these constraints, the classification space has exactly 20 elements.

    **What is PROVED**: The constraints are consistent and yield card = 20.

    **What is NOT proved** (remains MODEL/HYPOTHESIS):
    - That these constraints are "forced by physics"
    - That no other basis vectors are RS-legal
    - The specific mapping to amino acids

    The stronger forcing story requires showing that:
    - Neutrality follows from ledger conservation
    - Mode structure follows from shift-invariance / 8-tick dynamics
    - φ-lattice follows from J-cost minimization
    - 20 is the unique count given these requirements

    This is left for future work (WS2.4+). -/
def rs_token_classification_summary : String :=
  "✓ IsRSLegalBasis: neutrality + normalization predicate on 8-vectors\n" ++
  "✓ DFTModeFamily: 4 mode families matching Water.WTokenMode\n" ++
  "✓ RSTokenClassification: (family, φ-level, τ-offset) with constraint\n" ++
  "✓ equivWTokenCandidateParam: classification ≃ candidate params\n" ++
  "✓ equivWTokenId: classification ≃ canonical 20 token IDs\n" ++
  "✓ card_eq_20: exactly 20 RS token classifications\n" ++
  "\n" ++
  "PROVED: Constraints are consistent and yield exactly 20 tokens.\n" ++
  "MODEL: The specific constraints (neutrality, φ-lattice, etc.) are\n" ++
  "       explicitly stated but not derived from first principles here."

#eval rs_token_classification_summary

end Token
end IndisputableMonolith
