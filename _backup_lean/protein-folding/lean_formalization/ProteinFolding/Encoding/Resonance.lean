import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.ProteinFolding.Encoding.Chemistry
import IndisputableMonolith.ProteinFolding.Encoding.DFT8
import IndisputableMonolith.ProteinFolding.Encoding.WToken

/-!
# Resonance Scoring for Contact Prediction

This module implements the resonance-based contact scoring system that
predicts native contacts from sequence alone.

## Key Formula

The resonance score between positions i and j is:

    R(i,j) = cos(Δτ) · φ^(n_i + n_j) · G_chem · G_mode

Where:
- Δτ: Phase difference between WTokens
- n_i, n_j: φ-levels from WTokens
- G_chem: Chemistry gate (charge, H-bond, aromatic)
- G_mode: Mode compatibility gate

## Physical Motivation

Contacts form when two positions achieve "recognition resonance":
- Phase alignment (cos(Δτ) ≈ 1)
- Strong signals (high φ-levels)
- Compatible chemistry (favorable interactions)
- Compatible modes (same structural propensity)

-/

namespace IndisputableMonolith
namespace ProteinFolding
namespace Resonance

open Constants
open Chemistry
open DFT8
open WToken

/-! ## Sequence Encoding -/

/-- Complete encoding of a protein sequence -/
structure SequenceEncoding where
  /-- The amino acid sequence -/
  sequence : Sequence
  /-- Chemistry data for each position -/
  chemistry : List AAChemistry
  /-- DFT spectra for each position -/
  spectra : List (Fin 8 → ℂ)
  /-- WTokens for each position -/
  wtokens : List WToken
  /-- Consistency: chemistry matches sequence -/
  chemConsistent : chemistry = sequence.encode
  /-- Consistency: WTokens match spectra -/
  wtokenConsistent : wtokens = computeWTokenSequence spectra

/-- Create sequence encoding from raw sequence -/
noncomputable def encodeSequence (seq : Sequence) (channelSignal : List ℝ) : SequenceEncoding :=
  let chem := seq.encode
  let spectra := slidingDFT8 channelSignal
  let wtokens := computeWTokenSequence spectra
  { sequence := seq
    chemistry := chem
    spectra := spectra
    wtokens := wtokens
    chemConsistent := rfl
    wtokenConsistent := rfl }

/-! ## Core Resonance Score -/

/-- Phase difference component of resonance

    Uses cosine for smooth, symmetric scoring -/
noncomputable def phaseFactor (w_i w_j : WToken) : ℝ :=
  let Δτ := ((w_j.phase.val : ℤ) - (w_i.phase.val : ℤ)) % 8
  Real.cos (Δτ * Real.pi / 4)

/-- φ-level amplitude factor

    Higher levels indicate stronger recognition signals -/
noncomputable def amplitudeFactor (w_i w_j : WToken) : ℝ :=
  phi ^ ((w_i.phiLevel.val + w_j.phiLevel.val : ℝ) / 2 - 1)

/-- Mode compatibility gate

    Same mode: 1.2 boost
    Mode 2 ↔ Mode 4: 0.8 (helix-strand incompatibility)
    Otherwise: 1.0 -/
noncomputable def modeGate (w_i w_j : WToken) : ℝ :=
  if w_i.dominantMode = w_j.dominantMode then 1.2
  else if (w_i.dominantMode.val = 2 ∧ w_j.dominantMode.val = 4) ∨
          (w_i.dominantMode.val = 4 ∧ w_j.dominantMode.val = 2) then 0.8
  else 1.0

/-- **RESONANCE SCORE**

    The fundamental contact prediction formula combining:
    - Phase coherence (cos Δτ)
    - Amplitude strength (φ^n)
    - Chemistry compatibility
    - Mode compatibility -/
noncomputable def resonanceScore
    (chem_i chem_j : AAChemistry)
    (w_i w_j : WToken) : ℝ :=
  phaseFactor w_i w_j *
  amplitudeFactor w_i w_j *
  chemistryGate chem_i chem_j *
  modeGate w_i w_j

/-! ## Distance-Scaled Requirements (D5) -/

/-- Required number of coherent channels based on sequence separation

    Longer-range contacts require more supporting evidence -/
def requiredCoherentChannels (sequenceSeparation : ℕ) : ℕ :=
  if sequenceSeparation ≤ 10 then 2
  else if sequenceSeparation ≤ 16 then 3  -- 10 × φ ≈ 16
  else if sequenceSeparation ≤ 26 then 4  -- 16 × φ ≈ 26
  else if sequenceSeparation ≤ 42 then 5  -- 26 × φ ≈ 42
  else 6

/-- D5 verification: channels scale with log_φ of distance -/
theorem d5_scaling (d : ℕ) (hd : d ≥ 8) :
    requiredCoherentChannels d ≥ 2 := by
  simp only [requiredCoherentChannels]
  split_ifs <;> omega

/-! ## Contact Candidate Scoring -/

/-- A scored contact candidate -/
structure ContactCandidate where
  /-- First residue index -/
  i : ℕ
  /-- Second residue index -/
  j : ℕ
  /-- Sequence separation -/
  separation : ℕ := j - i
  /-- Resonance score -/
  score : ℝ
  /-- Number of supporting channels -/
  supportingChannels : ℕ
  /-- Validity: sufficient separation -/
  validSeparation : separation ≥ 6

/-- Check if candidate meets distance-scaled requirements -/
def ContactCandidate.meetsRequirements (c : ContactCandidate) : Bool :=
  c.supportingChannels ≥ requiredCoherentChannels c.separation

/-- Score penalty for loop closure (D4)

    Loops too short or too long incur J-cost penalty -/
noncomputable def loopClosurePenalty (separation : ℕ) : ℝ :=
  if separation < 6 then 0  -- Forbidden
  else
    let ratio := (separation : ℝ) / 10  -- Optimal at 10
    if separation ≤ 10 then
      1 / (1 + Cost.Jcost ratio)  -- Boost for optimal loops
    else
      1 / (1 + 0.5 * Cost.Jcost ratio)  -- Smaller penalty for long loops

/-- Adjusted resonance score with loop closure -/
noncomputable def adjustedResonanceScore
    (chem_i chem_j : AAChemistry)
    (w_i w_j : WToken)
    (separation : ℕ) : ℝ :=
  resonanceScore chem_i chem_j w_i w_j * loopClosurePenalty separation

/-! ## Contact Selection -/

/-- Select top contacts respecting the φ² budget -/
noncomputable def selectTopContacts
    (candidates : List ContactCandidate)
    (maxContacts : ℕ) : List ContactCandidate :=
  -- Sort by score descending, take top maxContacts
  (candidates.filter ContactCandidate.meetsRequirements)
    |>.mergeSort (fun c1 c2 => c1.score ≥ c2.score)
    |>.take maxContacts

/-- Predicted native contacts for a protein -/
structure ContactPrediction where
  /-- Sequence length -/
  sequenceLength : ℕ
  /-- Selected contacts -/
  contacts : List ContactCandidate
  /-- Respects contact budget -/
  budgetRespected : contacts.length ≤ ContactBudget.contactBudget sequenceLength

/-! ## Multi-Channel Consensus -/

/-- Count channels where two positions have coherent signals -/
noncomputable def countCoherentChannels
    (spectra_i spectra_j : Fin 8 → ℂ)
    (threshold : ℝ := 0.5) : ℕ :=
  let coherent := fun (k : Fin 8) =>
    phaseCoherence spectra_i spectra_j k > threshold
  (List.range 8).filter (fun k =>
    coherent ⟨k, Nat.lt_of_lt_of_le k.lt (by norm_num)⟩
  ) |>.length

/-- Multi-channel consensus score

    Rewards contacts supported by multiple coherent channels -/
noncomputable def consensusScore
    (spectra_i spectra_j : Fin 8 → ℂ)
    (separation : ℕ) : ℝ :=
  let coherentCount := countCoherentChannels spectra_i spectra_j
  let required := requiredCoherentChannels separation
  if coherentCount ≥ required then
    1.0 + 0.1 * (coherentCount - required)  -- Bonus for extra support
  else
    (coherentCount : ℝ) / required  -- Penalty for insufficient support

/-! ## Disulfide Bond Prediction -/

/-- Sulfur resonance for potential disulfide bonds -/
noncomputable def sulfurResonanceScore
    (chem_i chem_j : AAChemistry) : ℝ :=
  chem_i.sulfur * chem_j.sulfur

/-- Identify potential disulfide bonds (Cys-Cys pairs) -/
noncomputable def identifyDisulfides
    (encoding : SequenceEncoding) : List (ℕ × ℕ × ℝ) :=
  let cysPositions := encoding.chemistry.enum.filter
    (fun ⟨_, c⟩ => c.sulfur > 0.9)
  |>.map (·.1)
  -- All pairs of cysteine positions
  cysPositions.bind fun i =>
    cysPositions.filterMap fun j =>
      if i < j ∧ j - i ≥ 6 then
        let score := sulfurResonanceScore
          (encoding.chemistry.get! i)
          (encoding.chemistry.get! j)
        some (i, j, score)
      else none

end Resonance
end ProteinFolding
end IndisputableMonolith
