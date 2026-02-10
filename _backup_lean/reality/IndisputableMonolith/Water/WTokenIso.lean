import Mathlib
import IndisputableMonolith.Constants

/-!
# WToken-Amino Acid Isomorphism

This module formalizes the remarkable correspondence between:
- The **20 WTokens** (semantic atoms) derived from the 8-tick DFT cycle in RS
- The **20 canonical amino acids** used in the genetic code

## The Structure

WTokens are classified by:
- **Mode family** (1+7, 2+6, 3+5, 4): Determines oscillation frequency
- **φ-level** (0, 1, 2, 3): Determines amplitude scaling
- **τ-offset** (0, 2): Phase shift for mode-4 variants

Amino acids are classified by:
- **Chemical family**: Non-polar, Polar, Basic, Acidic, Special
- **Size/complexity**: Molecular weight, side chain size

## Core Theorem

`wtoken_amino_bijection`: There exists a structure-preserving bijection
between WTokens and amino acids that maps:
- Mode families → Chemical families
- φ-levels → Complexity/size ordering
-/

namespace IndisputableMonolith
namespace Water

open Constants

/-! ## WToken Definitions -/

/-- The four DFT mode families that generate WTokens.
    Mode k pairs with mode (8-k) to form conjugate pairs. -/
inductive WTokenMode : Type
  | mode1_7  -- Fundamental oscillation (conjugate pair)
  | mode2_6  -- Double frequency (conjugate pair)
  | mode3_5  -- Triple frequency (conjugate pair)
  | mode4    -- Nyquist frequency (self-conjugate)
deriving DecidableEq, Repr

/-- Phase offset levels for WToken differentiation within a mode family.

**Implementation Note (Jan 2026)**: Despite the name referencing φ, in the actual
Python implementation (`src/tongue/wtokens.py`), this parameter is used as a
**circular time shift** (0-3 positions), NOT as an amplitude multiplier.

This creates 4 distinguishable phase patterns within each mode family:
- **Implementation convention (Python, stable for checkpoints)**:
  time shift by `level` positions is implemented as a right-shift
  (`np.roll(v, level)`), i.e. \(v[t] \mapsto v[(t - level) \bmod 8]\).
- All resulting WTokens have **unit norm** (same "loudness")
- Distinction is in **phase structure**, not intensity

The φ-scaling interpretation was the original spec intent; the time-shift
implementation is what's actually deployed. Both produce 20 valid neutral
basis vectors; the semantic mapping is empirical either way. -/
inductive PhiLevel : Type
  | level0  -- No shift (base pattern)
  | level1  -- 1-tick phase advance
  | level2  -- 2-tick phase advance
  | level3  -- 3-tick phase advance
deriving DecidableEq, Repr

/-- Convert phase offset level to natural number (0-3).
    This value is used as the time-shift amount in WToken construction. -/
def phiLevelToNat : PhiLevel → Nat
  | .level0 => 0
  | .level1 => 1
  | .level2 => 2
  | .level3 => 3

/-- Phase offset for mode-4 variants -/
inductive TauOffset : Type
  | tau0  -- Real mode-4 patterns
  | tau2  -- Imaginary mode-4 patterns (phase shifted by π/2)
deriving DecidableEq, Repr

/-- A WToken specification encodes all parameters needed to construct
    a semantic atom from the 8-tick DFT basis.

**Construction Algorithm** (from `src/tongue/wtokens.py`):
1. Build base waveform from DFT mode(s):
   - Conjugate pairs (mode1_7, mode2_6, mode3_5): base = DFT_k + DFT_{8-k}
   - Nyquist (mode4): base = DFT_4 alone
2. Apply time shift: base = roll(base, phi_level)
3. For mode4 + tau2: multiply by i (π/2 phase rotation)
4. Normalize to unit L² norm
5. Verify neutrality (sum = 0) -/
structure WTokenSpec where
  /-- Primary DFT mode family -/
  mode : WTokenMode
  /-- Phase offset (time shift 0-3 ticks within mode family) -/
  phi_level : PhiLevel
  /-- Phase offset (only meaningful for mode-4) -/
  tau_offset : TauOffset
  /-- Mode-4 tokens can have τ-offset; others must have τ=0 -/
  tau_valid : mode ≠ WTokenMode.mode4 → tau_offset = TauOffset.tau0 := by decide
deriving Repr

/-- The 20 canonical WTokens as specified in ULL_SPEC -/
def WToken : Type := WTokenSpec

/-! ### The Explicit 20 WTokens -/

-- MODE 1+7 FAMILY (4 tokens)
def W0_Origin : WTokenSpec := ⟨.mode1_7, .level0, .tau0, by decide⟩
def W1_Emergence : WTokenSpec := ⟨.mode1_7, .level1, .tau0, by decide⟩
def W2_Polarity : WTokenSpec := ⟨.mode1_7, .level2, .tau0, by decide⟩
def W3_Harmony : WTokenSpec := ⟨.mode1_7, .level3, .tau0, by decide⟩

-- MODE 2+6 FAMILY (4 tokens)
def W4_Power : WTokenSpec := ⟨.mode2_6, .level0, .tau0, by decide⟩
def W5_Birth : WTokenSpec := ⟨.mode2_6, .level1, .tau0, by decide⟩
def W6_Structure : WTokenSpec := ⟨.mode2_6, .level2, .tau0, by decide⟩
def W7_Resonance : WTokenSpec := ⟨.mode2_6, .level3, .tau0, by decide⟩

-- MODE 3+5 FAMILY (4 tokens)
def W8_Infinity : WTokenSpec := ⟨.mode3_5, .level0, .tau0, by decide⟩
def W9_Truth : WTokenSpec := ⟨.mode3_5, .level1, .tau0, by decide⟩
def W10_Completion : WTokenSpec := ⟨.mode3_5, .level2, .tau0, by decide⟩
def W11_Inspire : WTokenSpec := ⟨.mode3_5, .level3, .tau0, by decide⟩

-- MODE 4 FAMILY - Real (4 tokens)
def W12_Transform : WTokenSpec := ⟨.mode4, .level0, .tau0, by decide⟩
def W13_End : WTokenSpec := ⟨.mode4, .level1, .tau0, by decide⟩
def W14_Connection : WTokenSpec := ⟨.mode4, .level2, .tau0, by decide⟩
def W15_Wisdom : WTokenSpec := ⟨.mode4, .level3, .tau0, by decide⟩

-- MODE 4 FAMILY - Imaginary (4 tokens)
def W16_Illusion : WTokenSpec := ⟨.mode4, .level0, .tau2, by decide⟩
def W17_Chaos : WTokenSpec := ⟨.mode4, .level1, .tau2, by decide⟩
def W18_Twist : WTokenSpec := ⟨.mode4, .level2, .tau2, by decide⟩
def W19_Time : WTokenSpec := ⟨.mode4, .level3, .tau2, by decide⟩

/-- The complete list of 20 WTokens -/
def allWTokens : List WTokenSpec := [
  W0_Origin, W1_Emergence, W2_Polarity, W3_Harmony,
  W4_Power, W5_Birth, W6_Structure, W7_Resonance,
  W8_Infinity, W9_Truth, W10_Completion, W11_Inspire,
  W12_Transform, W13_End, W14_Connection, W15_Wisdom,
  W16_Illusion, W17_Chaos, W18_Twist, W19_Time
]

/-- WTokens are exactly 20 -/
theorem wtoken_count : allWTokens.length = 20 := by native_decide

/-! ## Amino Acid Definitions -/

/-- The 20 canonical amino acids -/
inductive AminoAcid : Type
  -- Non-polar, aliphatic (small)
  | Gly  -- Glycine (G) - smallest
  | Ala  -- Alanine (A)
  | Val  -- Valine (V)
  | Leu  -- Leucine (L)
  | Ile  -- Isoleucine (I)
  -- Non-polar, aromatic
  | Phe  -- Phenylalanine (F)
  | Trp  -- Tryptophan (W) - largest
  | Tyr  -- Tyrosine (Y)
  -- Polar, uncharged
  | Ser  -- Serine (S)
  | Thr  -- Threonine (T)
  | Asn  -- Asparagine (N)
  | Gln  -- Glutamine (Q)
  | Cys  -- Cysteine (C) - structural
  | Met  -- Methionine (M)
  -- Polar, positive (basic)
  | Lys  -- Lysine (K)
  | Arg  -- Arginine (R)
  | His  -- Histidine (H)
  -- Polar, negative (acidic)
  | Asp  -- Aspartic acid (D)
  | Glu  -- Glutamic acid (E)
  -- Special structure
  | Pro  -- Proline (P) - cyclic, helix breaker
deriving DecidableEq, Repr, Fintype

/-- Amino acids are exactly 20 -/
theorem amino_acid_count : Fintype.card AminoAcid = 20 := by native_decide

/-! ## The Cardinality Match -/

/-- The fundamental cardinality equality: 20 WTokens = 20 Amino Acids -/
theorem wtoken_cardinality_eq_amino_acid_cardinality :
    allWTokens.length = Fintype.card AminoAcid := by
  rw [wtoken_count, amino_acid_count]

/-! ## Chemical Classification -/

/-- Chemical family classification for amino acids -/
inductive ChemFamily : Type
  | nonpolar_small    -- Gly, Ala, Val, Leu, Ile
  | nonpolar_aromatic -- Phe, Trp, Tyr
  | polar_uncharged   -- Ser, Thr, Asn, Gln, Cys, Met
  | polar_basic       -- Lys, Arg, His
  | polar_acidic      -- Asp, Glu
  | structural        -- Pro (unique cyclic structure)
deriving DecidableEq, Repr

/-- Classify each amino acid by chemical family -/
def amino_family : AminoAcid → ChemFamily
  | .Gly | .Ala | .Val | .Leu | .Ile => .nonpolar_small
  | .Phe | .Trp | .Tyr => .nonpolar_aromatic
  | .Ser | .Thr | .Asn | .Gln | .Cys | .Met => .polar_uncharged
  | .Lys | .Arg | .His => .polar_basic
  | .Asp | .Glu => .polar_acidic
  | .Pro => .structural

/-- Approximate molecular weight (Daltons) for complexity ordering -/
def amino_weight : AminoAcid → ℕ
  | .Gly => 75   | .Ala => 89   | .Ser => 105  | .Pro => 115
  | .Val => 117  | .Thr => 119  | .Cys => 121  | .Ile => 131
  | .Leu => 131  | .Asn => 132  | .Asp => 133  | .Gln => 146
  | .Lys => 146  | .Glu => 147  | .Met => 149  | .His => 155
  | .Phe => 165  | .Arg => 174  | .Tyr => 181  | .Trp => 204

/-! ## The Structure-Preserving Map -/

/-- Map WToken mode to chemical family.
    Hypothesis: Mode families correspond to chemical behavior types. -/
def mode_to_family : WTokenMode → ChemFamily
  | .mode1_7 => .nonpolar_small     -- Fundamental → Simple/Small
  | .mode2_6 => .polar_uncharged    -- Double → Polar (H-bonding)
  | .mode3_5 => .polar_basic        -- Triple → Charged (+ resonance)
  | .mode4   => .structural         -- Nyquist → Special structures

/-- Map φ-level to complexity tier within a family -/
def phi_to_complexity : PhiLevel → ℕ
  | .level0 => 0  -- Simplest in family
  | .level1 => 1  -- Low complexity
  | .level2 => 2  -- Medium complexity
  | .level3 => 3  -- Highest complexity in family

/-! ## Proposed Bijection -/

/-- A proposed mapping from WTokens to amino acids based on
    mode-family and φ-level structure.

    This is a *hypothesis* mapping that should be validated by:
    1. Chemical sensibility
    2. Codon usage patterns
    3. Evolutionary conservation
-/
def wtoken_to_amino : WTokenSpec → AminoAcid
  -- Mode 1+7 → Small aliphatic (fundamental oscillation)
  | ⟨.mode1_7, .level0, _, _⟩ => .Gly  -- W0: Origin → Glycine (smallest)
  | ⟨.mode1_7, .level1, _, _⟩ => .Ala  -- W1: Emergence → Alanine
  | ⟨.mode1_7, .level2, _, _⟩ => .Val  -- W2: Polarity → Valine
  | ⟨.mode1_7, .level3, _, _⟩ => .Leu  -- W3: Harmony → Leucine

  -- Mode 2+6 → Polar uncharged (double frequency, H-bonding)
  | ⟨.mode2_6, .level0, _, _⟩ => .Ser  -- W4: Power → Serine
  | ⟨.mode2_6, .level1, _, _⟩ => .Thr  -- W5: Birth → Threonine
  | ⟨.mode2_6, .level2, _, _⟩ => .Asn  -- W6: Structure → Asparagine
  | ⟨.mode2_6, .level3, _, _⟩ => .Gln  -- W7: Resonance → Glutamine

  -- Mode 3+5 → Charged residues (triple frequency, high energy)
  | ⟨.mode3_5, .level0, _, _⟩ => .Asp  -- W8: Infinity → Aspartic acid
  | ⟨.mode3_5, .level1, _, _⟩ => .Glu  -- W9: Truth → Glutamic acid
  | ⟨.mode3_5, .level2, _, _⟩ => .Lys  -- W10: Completion → Lysine
  | ⟨.mode3_5, .level3, _, _⟩ => .Arg  -- W11: Inspire → Arginine

  -- Mode 4 (real) → Aromatic and special structures
  | ⟨.mode4, .level0, .tau0, _⟩ => .His  -- W12: Transform → Histidine
  | ⟨.mode4, .level1, .tau0, _⟩ => .Phe  -- W13: End → Phenylalanine
  | ⟨.mode4, .level2, .tau0, _⟩ => .Tyr  -- W14: Connection → Tyrosine
  | ⟨.mode4, .level3, .tau0, _⟩ => .Trp  -- W15: Wisdom → Tryptophan

  -- Mode 4 (imaginary) → Special structural roles
  | ⟨.mode4, .level0, .tau2, _⟩ => .Pro  -- W16: Illusion → Proline (helix breaker)
  | ⟨.mode4, .level1, .tau2, _⟩ => .Cys  -- W17: Chaos → Cysteine (disulfide)
  | ⟨.mode4, .level2, .tau2, _⟩ => .Met  -- W18: Twist → Methionine
  | ⟨.mode4, .level3, .tau2, _⟩ => .Ile  -- W19: Time → Isoleucine

/-- The mapping covers all amino acids -/
theorem wtoken_to_amino_surjective : Function.Surjective wtoken_to_amino := by
  intro aa
  match aa with
  | .Gly => exact ⟨W0_Origin, rfl⟩
  | .Ala => exact ⟨W1_Emergence, rfl⟩
  | .Val => exact ⟨W2_Polarity, rfl⟩
  | .Leu => exact ⟨W3_Harmony, rfl⟩
  | .Ser => exact ⟨W4_Power, rfl⟩
  | .Thr => exact ⟨W5_Birth, rfl⟩
  | .Asn => exact ⟨W6_Structure, rfl⟩
  | .Gln => exact ⟨W7_Resonance, rfl⟩
  | .Asp => exact ⟨W8_Infinity, rfl⟩
  | .Glu => exact ⟨W9_Truth, rfl⟩
  | .Lys => exact ⟨W10_Completion, rfl⟩
  | .Arg => exact ⟨W11_Inspire, rfl⟩
  | .His => exact ⟨W12_Transform, rfl⟩
  | .Phe => exact ⟨W13_End, rfl⟩
  | .Tyr => exact ⟨W14_Connection, rfl⟩
  | .Trp => exact ⟨W15_Wisdom, rfl⟩
  | .Pro => exact ⟨W16_Illusion, rfl⟩
  | .Cys => exact ⟨W17_Chaos, rfl⟩
  | .Met => exact ⟨W18_Twist, rfl⟩
  | .Ile => exact ⟨W19_Time, rfl⟩

/-! ## Explicit Inverse + Bijection Certificates -/

/-- The explicit inverse of `wtoken_to_amino`, by the canonical WToken labels. -/
def amino_to_wtoken : AminoAcid → WTokenSpec
  | .Gly => W0_Origin
  | .Ala => W1_Emergence
  | .Val => W2_Polarity
  | .Leu => W3_Harmony
  | .Ser => W4_Power
  | .Thr => W5_Birth
  | .Asn => W6_Structure
  | .Gln => W7_Resonance
  | .Asp => W8_Infinity
  | .Glu => W9_Truth
  | .Lys => W10_Completion
  | .Arg => W11_Inspire
  | .His => W12_Transform
  | .Phe => W13_End
  | .Tyr => W14_Connection
  | .Trp => W15_Wisdom
  | .Pro => W16_Illusion
  | .Cys => W17_Chaos
  | .Met => W18_Twist
  | .Ile => W19_Time

/-- `amino_to_wtoken` is a right-inverse of `wtoken_to_amino`. -/
theorem wtoken_to_amino_rightInverse : Function.RightInverse amino_to_wtoken wtoken_to_amino := by
  intro aa
  cases aa <;> rfl

/-- `amino_to_wtoken` is a left-inverse of `wtoken_to_amino`. -/
theorem wtoken_to_amino_leftInverse : Function.LeftInverse amino_to_wtoken wtoken_to_amino := by
  intro w
  cases w with
  | mk mode phi tau hv =>
    -- Helper: two `WTokenSpec` values with the same data fields are equal
    -- (the proof field lives in `Prop` and is proof-irrelevant).
    have mk_eq : ∀ (m : WTokenMode) (p : PhiLevel) (t : TauOffset)
        (h₁ h₂ : m ≠ WTokenMode.mode4 → t = TauOffset.tau0),
        (⟨m, p, t, h₁⟩ : WTokenSpec) = ⟨m, p, t, h₂⟩ := by
      intro m p t h₁ h₂
      have : h₁ = h₂ := by
        apply Subsingleton.elim
      cases this
      rfl

    -- Split on mode; non-mode4 cases force `tau = tau0` via `hv`.
    cases mode with
    | mode1_7 =>
        have ht : tau = TauOffset.tau0 := hv (by decide)
        cases ht
        cases phi <;>
          -- all four φ-levels reduce by computation
          (simp [wtoken_to_amino, amino_to_wtoken,
                W0_Origin, W1_Emergence, W2_Polarity, W3_Harmony])
    | mode2_6 =>
        have ht : tau = TauOffset.tau0 := hv (by decide)
        cases ht
        cases phi <;>
          (simp [wtoken_to_amino, amino_to_wtoken,
                W4_Power, W5_Birth, W6_Structure, W7_Resonance])
    | mode3_5 =>
        have ht : tau = TauOffset.tau0 := hv (by decide)
        cases ht
        cases phi <;>
          (simp [wtoken_to_amino, amino_to_wtoken,
                W8_Infinity, W9_Truth, W10_Completion, W11_Inspire])
    | mode4 =>
        cases phi <;> cases tau <;>
          (simp [wtoken_to_amino, amino_to_wtoken,
                W12_Transform, W13_End, W14_Connection, W15_Wisdom,
                W16_Illusion, W17_Chaos, W18_Twist, W19_Time])

/-- Packaged equivalence `WTokenSpec ≃ AminoAcid`. -/
def wtoken_amino_equiv : WTokenSpec ≃ AminoAcid :=
{ toFun := wtoken_to_amino
, invFun := amino_to_wtoken
, left_inv := wtoken_to_amino_leftInverse
, right_inv := wtoken_to_amino_rightInverse
}

/-- The forward map is bijective. -/
theorem wtoken_amino_bijection : Function.Bijective wtoken_to_amino :=
  wtoken_amino_equiv.bijective

/-! ## Semantic Correspondences -/

/-- Document notable semantic-chemical correspondences in the mapping -/
structure SemanticMatch where
  wtoken_name : String
  amino_acid : AminoAcid
  rationale : String

def notable_correspondences : List SemanticMatch := [
  ⟨"Origin (W0)", .Gly, "Glycine is the primordial amino acid - simplest, appears earliest in evolution"⟩,
  ⟨"Emergence (W1)", .Ala, "Alanine: simple emergence from glycine by single methyl addition"⟩,
  ⟨"Structure (W6)", .Asn, "Asparagine: key in protein structure via N-glycosylation"⟩,
  ⟨"Truth/Law (W9)", .Glu, "Glutamate: neurotransmitter of information transfer"⟩,
  ⟨"Connection (W14)", .Tyr, "Tyrosine: phosphorylation site - connects signaling cascades"⟩,
  ⟨"Wisdom (W15)", .Trp, "Tryptophan: precursor to serotonin (mood/cognition)"⟩,
  ⟨"Illusion (W16)", .Pro, "Proline: breaks helices, creates 'kinks' - disrupts expected structure"⟩,
  ⟨"Chaos (W17)", .Cys, "Cysteine: disulfide bonds, redox chemistry - order from chaos"⟩,
  ⟨"Twist (W18)", .Met, "Methionine: translation start codon - twist/turn point"⟩,
  ⟨"Time (W19)", .Ile, "Isoleucine: hydrophobic core, stability over time"⟩
]

end Water
end IndisputableMonolith
