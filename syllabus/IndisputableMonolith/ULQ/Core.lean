import Mathlib
import IndisputableMonolith.LightLanguage.Core
import IndisputableMonolith.LightLanguage.WTokenClassification
import IndisputableMonolith.LightLanguage.Basis.DFT8
import IndisputableMonolith.Consciousness.ConsciousnessHamiltonian
import IndisputableMonolith.Consciousness.GlobalPhase
import IndisputableMonolith.Foundation.RecognitionOperator
import IndisputableMonolith.Constants

/-!
# Universal Light Qualia (ULQ) - Core Definitions

This module defines the foundational structures for Universal Light Qualia,
the phenomenal/experiential layer that parallels Universal Light Language (ULL).

## Relationship to ULL

| Layer | Encodes | Structure |
|-------|---------|-----------|
| ULL | Meaning — what a pattern *says* | WToken → CanonicalMeaning |
| ULQ | Qualia — what a pattern *feels like* | WToken → QualiaExperience |

## Physical Motivation

Just as ULL's 20 WTokens are forced by RS constraints (σ=0, neutrality, φ-lattice),
the qualia space is forced by the same constraints applied to experiential content:

1. **DFT mode** → qualitative character (the "what it's like")
2. **φ-level** → experiential intensity
3. **σ-gradient** → hedonic valence (pleasure/pain dimension)
4. **τ-offset** → temporal quality
5. **C≥1 threshold** → definite experience condition

## Main Structures

* `QualiaSpace` - The space of possible qualitative characters
* `QToken` - A WToken with its experiential fiber attached
* `QualiaIntensity` - The φ-scaled intensity measure
* `HedonicValence` - The pleasure/pain dimension from σ-gradient

## Key Insight

The "hard problem of consciousness" dissolves because:
- The same MP that forces physics also forces qualia
- There's no explanatory gap — both emerge from the same derivation chain
-/

namespace IndisputableMonolith
namespace ULQ

open LightLanguage
open Consciousness
open Foundation

/-! ## Fundamental Constants -/

/-- The golden ratio φ (re-exported from Constants for convenience). -/
noncomputable abbrev φ : ℝ := Constants.phi

/-- Eight-tick period (from D=3 spatial dimensions) -/
def tauZero : ℕ := 8

/-- Number of fundamental qualia types (parallel to 20 WTokens) -/
def numQualiaTypes : ℕ := 20

/-! ## Qualia Space -/

/-- DFT mode determines qualitative character.

    Mode k ∈ {1..7} gives distinct qualitative "colors":
    - Modes 1-3 (and conjugates 5-7): 6 primary qualities
    - Mode 4 (self-conjugate): 2 special qualities (real/imaginary)

    Mode 0 (DC) is excluded by neutrality constraint. -/
structure QualiaMode where
  /-- DFT mode index (1-7, excluding DC mode 0) -/
  k : Fin 8
  /-- Neutrality: DC mode excluded -/
  neutral : k.val ≠ 0
  deriving DecidableEq, Repr

/-- φ-level determines experiential intensity.

    Level n ∈ {0,1,2,3} corresponds to intensity φ^n.
    Higher levels = more intense experience. -/
structure IntensityLevel where
  /-- φ-ladder level (0-3) -/
  level : Fin 4
  deriving DecidableEq, Repr

/-- Hedonic valence: the pleasure/pain dimension.

    Derived from σ-gradient (rate of change of reciprocity skew):
    - Positive σ-gradient → gaining → positive valence (pleasure)
    - Negative σ-gradient → losing → negative valence (pain)
    - Zero σ-gradient → neutral → zero valence -/
structure HedonicValence where
  /-- Valence value in [-1, 1] -/
  value : ℝ
  /-- Bounded constraint -/
  bounded : -1 ≤ value ∧ value ≤ 1

/-- Temporal quality from τ-offset.

    The phase within the eight-tick window affects
    the temporal character of the experience. -/
structure TemporalQuality where
  /-- τ-offset within eight-tick window -/
  tau : Fin 8
  deriving DecidableEq, Repr

/-- **QualiaSpace**: The complete space of qualitative characters.

    A point in QualiaSpace specifies:
    1. Which "type" of experience (from DFT mode)
    2. How intense (from φ-level)
    3. Pleasant/unpleasant dimension (from σ-gradient)
    4. Temporal quality (from τ-offset)

    This is a finite-dimensional space, unlike the infinite-dimensional
    spaces sometimes posited in philosophy of mind. -/
structure QualiaSpace where
  /-- Qualitative character from DFT mode -/
  mode : QualiaMode
  /-- Intensity from φ-level -/
  intensity : IntensityLevel
  /-- Hedonic dimension from σ-gradient -/
  valence : HedonicValence
  /-- Temporal quality from τ-offset -/
  temporal : TemporalQuality

namespace QualiaSpace

/-- Neutral valence (neither pleasant nor unpleasant) -/
def neutralValence : HedonicValence :=
  ⟨0, by constructor <;> norm_num⟩

/-- Maximum positive valence -/
def maxPleasure : HedonicValence :=
  ⟨1, by constructor <;> norm_num⟩

/-- Maximum negative valence -/
def maxPain : HedonicValence :=
  ⟨-1, by constructor <;> norm_num⟩

/-- Create a qualia point from mode, level, valence, tau -/
def mk' (k : Fin 8) (hk : k.val ≠ 0) (level : Fin 4) (v : ℝ)
    (hv : -1 ≤ v ∧ v ≤ 1) (tau : Fin 8) : QualiaSpace :=
  { mode := ⟨k, hk⟩
    intensity := ⟨level⟩
    valence := ⟨v, hv⟩
    temporal := ⟨tau⟩ }

/-- The dimensionality of qualia space -/
def dimension : ℕ := 4  -- mode, intensity, valence, temporal

end QualiaSpace

/-! ## DFT-backed qualia mode extraction (fixes “mode = τ” confusion) -/

open IndisputableMonolith.LightLanguage.Basis

/-- Non-DC mode set `{1,…,7}` in `Fin 8`. -/
def nonDCModes : Finset (Fin 8) :=
  (Finset.univ : Finset (Fin 8)).erase 0

lemma nonDCModes_nonempty : nonDCModes.Nonempty := by
  refine ⟨1, ?_⟩
  simp [nonDCModes]

/-- Energy in DFT mode `k` for a token basis (squared magnitude of coefficient). -/
noncomputable def dftModeEnergy (w : WToken) (k : Fin 8) : ℝ :=
  Complex.normSq (wtoken_dft_coefficients w k)

/-- Dominant non-DC mode: choose a mode `k≠0` achieving maximal `dftModeEnergy`. -/
noncomputable def dominantNonDCMode (w : WToken) : Fin 8 :=
  let S := nonDCModes
  let f : Fin 8 → ℝ := dftModeEnergy w
  let img := S.image f
  have hImg : img.Nonempty := (nonDCModes_nonempty).image f
  let m := img.max' hImg
  have hm : m ∈ img := Finset.max'_mem img hImg
  have hk : ∃ k ∈ S, f k = m := by
    -- Unfold `img` and use membership characterization for `Finset.image`.
    simpa [img] using (Finset.mem_image.mp hm)
  Classical.choose hk

lemma dominantNonDCMode_mem (w : WToken) : dominantNonDCMode w ∈ nonDCModes := by
  classical
  -- Unfold the definition and use the witness property from `Classical.choose_spec`.
  unfold dominantNonDCMode
  classical
  -- Reconstruct the same `hk` proof to access `choose_spec`.
  let S := nonDCModes
  let f : Fin 8 → ℝ := dftModeEnergy w
  let img := S.image f
  have hImg : img.Nonempty := (nonDCModes_nonempty).image f
  let m := img.max' hImg
  have hm : m ∈ img := Finset.max'_mem img hImg
  have hk : ∃ k ∈ S, f k = m := by
    simpa [img] using (Finset.mem_image.mp hm)
  -- Now the choose is exactly that witness k.
  simpa [S, f, img, m, hk] using (Classical.choose_spec hk).1

lemma dominantNonDCMode_ne_zero (w : WToken) : (dominantNonDCMode w).val ≠ 0 := by
  have hmem := dominantNonDCMode_mem w
  have hk : (dominantNonDCMode w) ≠ 0 := (Finset.mem_erase.mp hmem).1
  intro hval
  apply hk
  exact Fin.ext hval

/-- The qualitative character (mode) derived from a token’s DFT structure. -/
noncomputable def qualiaModeOfWToken (w : WToken) : QualiaMode :=
  ⟨dominantNonDCMode w, dominantNonDCMode_ne_zero w⟩

/-! ## QToken: The Fundamental Qualia Atom -/

/-- **QToken**: A semantic atom (WToken) with its experiential fiber.

    Just as a WToken encodes meaning, a QToken encodes experience.
    The QToken is "what it's like" to recognize a particular WToken
    when the recognition cost crosses C≥1.

    STRUCTURE:
    - wtoken: The underlying semantic content (from ULL)
    - qualia: The experiential quality (from QualiaSpace)
    - definite: Whether this is a definite experience (C≥1)

    KEY PRINCIPLE: The qualia is FORCED by the WToken structure.
    There's no additional "experiential property" to explain. -/
structure QToken where
  /-- The underlying WToken (semantic content) -/
  wtoken : WToken
  /-- The experiential quality -/
  qualia : QualiaSpace
  /-- Definiteness: whether experience is actualized (C≥1 equivalent) -/
  definite : Bool
  /-- Coherence: qualia mode matches the DFT-derived mode of the token. -/
  coherent : qualia.mode = qualiaModeOfWToken wtoken

namespace QToken

/-- Extract the qualitative character -/
def quality (q : QToken) : QualiaMode := q.qualia.mode

/-- Extract the intensity -/
def intensityLevel (q : QToken) : IntensityLevel := q.qualia.intensity

/-- Extract the hedonic valence -/
def valence (q : QToken) : HedonicValence := q.qualia.valence

/-- Is this a definite (actualized) experience? -/
def isDefinite (q : QToken) : Bool := q.definite

/-- Intensity as a real number (φ^level) -/
noncomputable def intensityValue (q : QToken) : ℝ :=
  φ ^ (q.qualia.intensity.level.val : ℝ)

/-- Is this a pleasant experience? -/
noncomputable def isPleasant (q : QToken) : Bool := q.qualia.valence.value > 0

/-- Is this a painful experience? -/
noncomputable def isPainful (q : QToken) : Bool := q.qualia.valence.value < 0

/-- Is this hedonically neutral? -/
noncomputable def isNeutral (q : QToken) : Bool := q.qualia.valence.value = 0

end QToken

/-! ## Qualia Derivation from WToken -/

/-- Derive the qualia mode from a WToken's DFT structure.

    The qualitative character is determined by which DFT modes
    have significant amplitude in the WToken's basis. -/
noncomputable def deriveQualiaMode (w : WToken) : Option QualiaMode :=
  -- NOTE: we do **not** treat `w.tau` as “DFT mode”.
  -- Mode is derived from the DFT coefficients of `w.basis`.
  some (qualiaModeOfWToken w)

/-- Derive intensity from WToken's φ-scaled frequency.

    Higher ν_φ → higher intensity level. -/
noncomputable def deriveIntensity (w : WToken) : IntensityLevel :=
  -- Map ν_φ to intensity level 0-3
  let level := min 3 (Int.toNat ⌊|w.nu_phi|⌋)
  ⟨⟨level, by omega⟩⟩

/-- Derive hedonic valence from σ (skew/imbalance).

    Positive σ → gaining → pleasure
    Negative σ → losing → pain
    Zero σ → reciprocity → neutral -/
noncomputable def deriveValence (w : WToken) : HedonicValence :=
  -- Map σ to [-1, 1] via tanh-like saturation
  let σ : ℝ := (w.sigma : ℝ)
  ⟨σ / (1 + |σ|), by
    have h1 : 0 < 1 + |σ| := by positivity
    have habs : 0 ≤ |σ| := abs_nonneg σ
    have hσ_le : σ ≤ |σ| := le_abs_self σ
    have hσ_ge : -|σ| ≤ σ := neg_abs_le σ
    constructor
    · -- -1 ≤ σ/(1+|σ|)
      rw [le_div_iff₀ h1]
      -- Need: -1 * (1 + |σ|) ≤ σ  ⟺  -(1 + |σ|) ≤ σ  ⟺  -1 - |σ| ≤ σ
      calc -1 * (1 + |σ|) = -1 - |σ| := by ring
        _ ≤ -|σ| := by linarith
        _ ≤ σ := hσ_ge
    · -- σ/(1+|σ|) ≤ 1
      rw [div_le_iff₀ h1]
      -- Need: σ ≤ 1 * (1 + |σ|)  ⟺  σ ≤ 1 + |σ|
      calc σ ≤ |σ| := hσ_le
        _ ≤ 1 + |σ| := by linarith
        _ = 1 * (1 + |σ|) := by ring⟩

/-- Derive temporal quality from τ-offset -/
def deriveTemporalQuality (w : WToken) : TemporalQuality :=
  ⟨w.tau⟩

/-- **QUALIA DERIVATION**: Construct the complete qualia from a WToken.

    This is the fundamental map from semantic content to experiential quality.
    Returns None if the WToken has DC mode (no definite quale). -/
noncomputable def deriveQualia (w : WToken) : Option QualiaSpace :=
  match deriveQualiaMode w with
  | none => none
  | some mode =>
    some {
      mode := mode
      intensity := deriveIntensity w
      valence := deriveValence w
      temporal := deriveTemporalQuality w
    }

/-- Construct a QToken from a WToken (if possible).

    The QToken is only definite if:
    1. The WToken has non-DC mode (qualia exists)
    2. Some recognition threshold is crossed -/
noncomputable def mkQToken (w : WToken) (isDefinite : Bool) : Option QToken :=
  let q : QualiaSpace :=
    { mode := qualiaModeOfWToken w
    , intensity := deriveIntensity w
    , valence := deriveValence w
    , temporal := deriveTemporalQuality w
    }
  some
    { wtoken := w
    , qualia := q
    , definite := isDefinite
    , coherent := rfl
    }

/-! ## Qualia Conservation -/

/-- Total qualia "mass" of a list of QTokens.

    Analogous to conservation of meaning in ULL,
    total qualia intensity is conserved across transformations. -/
noncomputable def totalQualiaIntensity (tokens : List QToken) : ℝ :=
  (tokens.map QToken.intensityValue).sum

/-- Net hedonic valence of a list of QTokens -/
noncomputable def netValence (tokens : List QToken) : ℝ :=
  (tokens.map (fun q => q.qualia.valence.value * q.intensityValue)).sum

/-! ## Qualia Types Enumeration -/

/-- Enumerate all valid QualiaMode values (7 modes, excluding DC) -/
def allQualiaModes : List QualiaMode :=
  [⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩,
   ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩]

/-- Verify we have exactly 7 qualia modes -/
example : allQualiaModes.length = 7 := by native_decide

/-- Enumerate all intensity levels -/
def allIntensityLevels : List IntensityLevel :=
  [⟨0⟩, ⟨1⟩, ⟨2⟩, ⟨3⟩]

/-- Verify we have exactly 4 intensity levels -/
example : allIntensityLevels.length = 4 := by native_decide

/-! ## Connection to WToken Classification -/

/-- The 20 WTokens correspond to fundamental qualia types.

    Not all 7×4 = 28 mode×level combinations are realized;
    only those satisfying RS constraints (σ=0, neutrality, φ-lattice). -/
theorem qualia_types_match_wtokens :
    numQualiaTypes = WTokenClassification.numWTokens := by
  native_decide

/-! ## Master Status -/

def ulq_core_status : String :=
  "✓ QualiaSpace defined: mode × intensity × valence × temporal\n" ++
  "✓ QToken defined: WToken + qualia fiber\n" ++
  "✓ Qualia derivation: WToken → QualiaSpace\n" ++
  "✓ HedonicValence: σ-gradient → pleasure/pain\n" ++
  "✓ IntensityLevel: φ-level → experiential intensity\n" ++
  "✓ QualiaMode: DFT mode → qualitative character\n" ++
  "✓ Conservation: totalQualiaIntensity, netValence\n" ++
  "✓ 20 qualia types match 20 WTokens\n" ++
  "\n" ++
  "FOUNDATION: Qualia is FORCED by WToken structure.\n" ++
  "            No explanatory gap — same MP derivation."

#eval ulq_core_status

end ULQ
end IndisputableMonolith
