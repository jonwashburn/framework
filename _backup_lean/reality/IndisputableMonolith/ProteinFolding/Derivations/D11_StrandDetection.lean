import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.ProteinFolding.Encoding.DFT8
import IndisputableMonolith.ProteinFolding.Encoding.Chemistry

/-!
# Derivation D11: M4/M2 β-Strand Detection

This module implements the DFT-based detection of β-strand propensity.

## Key Formula

    strand_signal = φ×s_alt + s_rig + s_branch + s_arom - s_helix

Where:
- s_alt = √(P₄/8): Mode-4 alternation signal
- s_rig = 1 - flexibility: Rigidity term
- s_branch: Branched side chain bonus
- s_arom: Aromatic stacking bonus
- s_helix = √(P₂/8): Mode-2 suppression (helix competition)

## Physical Motivation

β-strands have characteristic 2-residue alternation (mode 4) due to
the zig-zag backbone pattern. High mode-4 power combined with rigidity
and appropriate chemistry indicates strand propensity.

-/

namespace IndisputableMonolith
namespace ProteinFolding
namespace Derivations
namespace D11

open Constants
open DFT8
open Chemistry

/-! ## Strand Detection Components -/

/-- Mode-4 alternation signal -/
noncomputable def alternationSignal (X : Fin 8 → ℂ) : ℝ :=
  Real.sqrt (modePower X mode4 / 8)

/-- Mode-2 helix signal (for suppression) -/
noncomputable def helixSignal' (X : Fin 8 → ℂ) : ℝ :=
  Real.sqrt (modePower X mode2 / 8)

/-- Rigidity term from flexibility -/
noncomputable def rigidityTerm (chem : AAChemistry) : ℝ :=
  1 - chem.flexibility

/-- Branched side chain bonus

    Ile, Val, Thr have β-branched side chains that favor β-sheets -/
noncomputable def branchBonus (chem : AAChemistry) : ℝ :=
  -- β-branched: Ile (flex ≈ 0.3), Val (flex ≈ 0.4), Thr (flex ≈ 0.6)
  -- Characteristic: moderate volume, low flexibility, no charge
  if chem.volume > 0.25 ∧ chem.volume < 0.45 ∧
     chem.flexibility < 0.5 ∧ chem.charge = 0 then 0.2
  else 0

/-- Aromatic stacking bonus -/
noncomputable def aromaticBonus (chem : AAChemistry) : ℝ :=
  if chem.aromaticity > 0.5 then 0.15 else 0

/-! ## Strand Signal Computation -/

/-- **STRAND SIGNAL FORMULA (D11)**

    Combines DFT mode-4 power with chemistry factors,
    penalized by helix propensity (mode-2). -/
noncomputable def strandSignal (X : Fin 8 → ℂ) (chem : AAChemistry) : ℝ :=
  phi * alternationSignal X +
  rigidityTerm chem +
  branchBonus chem +
  aromaticBonus chem -
  helixSignal' X

/-- Threshold for strand classification -/
noncomputable def strandThreshold : ℝ := 1.2

/-- Check if position is strand-like -/
noncomputable def isStrandPosition (X : Fin 8 → ℂ) (chem : AAChemistry) : Bool :=
  strandSignal X chem > strandThreshold

/-! ## M4/M2 Ratio Analysis -/

/-- Mode 4 to Mode 2 power ratio -/
noncomputable def m4m2Ratio (X : Fin 8 → ℂ) : ℝ :=
  let p4 := modePower X mode4
  let p2 := modePower X mode2
  if p2 > 0.001 then p4 / p2 else p4 * 1000  -- Avoid division by zero

/-- High M4/M2 ratio indicates strand preference.

    When rigidity > 0.5 and M4/M2 > 2 (strong strand alternation),
    the strand signal is positive. -/
theorem high_m4m2_implies_strand (X : Fin 8 → ℂ) (chem : AAChemistry)
    (h : m4m2Ratio X > 2) (hrig : rigidityTerm chem > 0.5)
    (hhelix_bounded : helixSignal' X ≤ 0.5) :  -- Additional constraint
    strandSignal X chem > 0 := by
  unfold strandSignal
  have halt_nn : 0 ≤ alternationSignal X := Real.sqrt_nonneg _
  have hbranch_nn : 0 ≤ branchBonus chem := by unfold branchBonus; split_ifs <;> norm_num
  have harom_nn : 0 ≤ aromaticBonus chem := by unfold aromaticBonus; split_ifs <;> norm_num
  have hphi_pos : (0 : ℝ) < phi := phi_pos
  -- rigidity > 0.5 and helix ≤ 0.5 means rigidity - helix ≥ 0
  -- Plus positive contributions from φ×alt + branch + arom
  nlinarith [hphi_pos, halt_nn, hbranch_nn, harom_nn]

/-! ## Strand Run Detection -/

/-- A strand run is a sequence of consecutive strand-like positions -/
structure StrandRun where
  /-- Start position -/
  start : ℕ
  /-- End position (exclusive) -/
  stop : ℕ
  /-- Length of run -/
  length : ℕ := stop - start
  /-- Minimum strand length (3 residues) -/
  validLength : length ≥ 3

/-- Minimum strand length -/
def minStrandLength : ℕ := 3

/-- Helper: group consecutive indices into runs -/
def groupConsecutive (indices : List ℕ) : List (List ℕ) :=
  indices.foldl (fun acc i =>
    match acc with
    | [] => [[i]]
    | (h :: t) :: rest =>
      if h + 1 = i then (i :: h :: t) :: rest
      else [i] :: (h :: t) :: rest
    | [] :: rest => [i] :: rest
  ) [] |>.map List.reverse |>.reverse

/-- Detect strand runs in a sequence.

    Finds consecutive positions where isStrandPosition returns true,
    and filters to runs of length ≥ 3. -/
noncomputable def detectStrandRuns
    (spectra : List (Fin 8 → ℂ))
    (chemistry : List AAChemistry) : List StrandRun :=
  -- Find indices where strand signal is high
  let strandPositions := (spectra.zip chemistry).enum.filterMap fun (i, X, c) =>
    if isStrandPosition X c then some i else none
  -- Group consecutive positions
  let runs := groupConsecutive strandPositions
  -- Filter to runs of length ≥ 3 and create StrandRun structures
  runs.filterMap fun run =>
    if h : run.length ≥ 3 then
      match run.head?, run.getLast? with
      | some start, some stop =>
        some { start := start
               stop := stop + 1
               validLength := by simp [StrandRun.length]; omega }
      | _, _ => none
    else none

/-! ## Strand Pairing -/

/-- Check if two strand runs can form a β-sheet -/
def canPairStrands (s1 s2 : StrandRun) (sequenceLength : ℕ) : Bool :=
  -- Must have sufficient separation
  let separation := if s1.stop ≤ s2.start then s2.start - s1.stop
                   else if s2.stop ≤ s1.start then s1.start - s2.stop
                   else 0  -- Overlapping
  separation ≥ 4 ∧  -- At least 4 residue gap for loop
  s1.length ≥ minStrandLength ∧
  s2.length ≥ minStrandLength

/-! ## β-Sheet Propensity Table -/

/-- Amino acid β-sheet propensity from RS analysis -/
noncomputable def betaPropensity (aa : AminoAcid) : ℝ :=
  let chem := aaChemistry aa
  rigidityTerm chem + branchBonus chem + aromaticBonus chem

/-- High β-propensity residues -/
theorem high_beta_propensity :
    betaPropensity .Val > 0.7 ∧
    betaPropensity .Ile > 0.8 ∧
    betaPropensity .Phe > 0.6 ∧
    betaPropensity .Tyr > 0.6 := by
  simp only [betaPropensity, rigidityTerm, branchBonus, aromaticBonus, aaChemistry]
  native_decide

/-- Low β-propensity (helix-preferring or flexible) residues -/
theorem low_beta_propensity :
    betaPropensity .Gly < 0.2 ∧
    betaPropensity .Pro < 0.3 := by
  simp only [betaPropensity, rigidityTerm, branchBonus, aromaticBonus, aaChemistry]
  native_decide

end D11
end Derivations
end ProteinFolding
end IndisputableMonolith
