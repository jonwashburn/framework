import Mathlib
import IndisputableMonolith.Constants

/-!
# The Eight Chemistry Channels

This module formalizes the amino acid representation system using 8 chemistry
channels that encode the physical properties of each residue.

## The Channels

| Channel | Property | Range | Description |
|---------|----------|-------|-------------|
| 0 | Volume | [0,1] | Normalized van der Waals volume |
| 1 | Charge | [-1,1] | pH 7 ionization charge |
| 2 | Polarity | [0,1] | Dipole moment (normalized) |
| 3 | H-donors | [0,1] | N-H and O-H count (normalized) |
| 4 | H-acceptors | [0,1] | C=O, N, O count (normalized) |
| 5 | Aromaticity | {0,1} | Aromatic ring presence |
| 6 | Flexibility | [0,1] | χ-angle rotational freedom |
| 7 | Sulfur | {0,0.5,1} | Sulfur content (none/thiol/thioether) |

## Physical Motivation

These 8 channels capture the chemistry relevant for protein folding:
- Steric: Volume determines packing
- Electrostatic: Charge and polarity for salt bridges and H-bonds
- H-bonding: Donor/acceptor counts for secondary structure
- Aromatic: π-stacking and cation-π interactions
- Entropy: Flexibility affects folding dynamics
- Disulfides: Sulfur for covalent cross-links

-/

namespace IndisputableMonolith
namespace ProteinFolding
namespace Chemistry

/-! ## Basic Types -/

/-- Unit interval [0, 1] for normalized properties -/
structure UnitInterval where
  val : ℝ
  nonneg : 0 ≤ val
  le_one : val ≤ 1

instance : Coe UnitInterval ℝ := ⟨UnitInterval.val⟩

/-- Signed unit interval [-1, 1] for charge -/
structure SignedUnitInterval where
  val : ℝ
  ge_neg_one : -1 ≤ val
  le_one : val ≤ 1

instance : Coe SignedUnitInterval ℝ := ⟨SignedUnitInterval.val⟩

/-- Sulfur content type -/
inductive SulfurContent
  | none      -- No sulfur
  | thiol     -- Cysteine -SH (can form disulfides)
  | thioether -- Methionine -S-CH₃
  deriving DecidableEq, Repr

/-- Convert sulfur content to numeric value -/
def SulfurContent.toReal : SulfurContent → ℝ
  | .none => 0
  | .thiol => 1.0      -- Full disulfide potential
  | .thioether => 0.5  -- Partial (no disulfide, but hydrophobic)

/-! ## The 20 Amino Acids -/

/-- The 20 standard amino acids -/
inductive AminoAcid
  | Ala | Cys | Asp | Glu | Phe   -- A, C, D, E, F
  | Gly | His | Ile | Lys | Leu   -- G, H, I, K, L
  | Met | Asn | Pro | Gln | Arg   -- M, N, P, Q, R
  | Ser | Thr | Val | Trp | Tyr   -- S, T, V, W, Y
  deriving DecidableEq, Repr

/-- One-letter code for amino acids -/
def AminoAcid.code : AminoAcid → Char
  | .Ala => 'A' | .Cys => 'C' | .Asp => 'D' | .Glu => 'E' | .Phe => 'F'
  | .Gly => 'G' | .His => 'H' | .Ile => 'I' | .Lys => 'K' | .Leu => 'L'
  | .Met => 'M' | .Asn => 'N' | .Pro => 'P' | .Gln => 'Q' | .Arg => 'R'
  | .Ser => 'S' | .Thr => 'T' | .Val => 'V' | .Trp => 'W' | .Tyr => 'Y'

/-- Three-letter code for amino acids -/
def AminoAcid.code3 : AminoAcid → String
  | .Ala => "ALA" | .Cys => "CYS" | .Asp => "ASP" | .Glu => "GLU" | .Phe => "PHE"
  | .Gly => "GLY" | .His => "HIS" | .Ile => "ILE" | .Lys => "LYS" | .Leu => "LEU"
  | .Met => "MET" | .Asn => "ASN" | .Pro => "PRO" | .Gln => "GLN" | .Arg => "ARG"
  | .Ser => "SER" | .Thr => "THR" | .Val => "VAL" | .Trp => "TRP" | .Tyr => "TYR"

/-! ## Eight-Channel Chemistry Encoding -/

/-- Complete chemistry encoding for an amino acid -/
structure AAChemistry where
  /-- Channel 0: Normalized van der Waals volume [0,1] -/
  volume : ℝ
  /-- Channel 1: pH 7 charge [-1,1] -/
  charge : ℝ
  /-- Channel 2: Polarity/dipole moment [0,1] -/
  polarity : ℝ
  /-- Channel 3: H-bond donors (N-H, O-H) [0,1] -/
  hDonors : ℝ
  /-- Channel 4: H-bond acceptors (C=O, N, O) [0,1] -/
  hAcceptors : ℝ
  /-- Channel 5: Aromaticity (0 or 1) -/
  aromaticity : ℝ
  /-- Channel 6: Flexibility (χ-angle freedom) [0,1] -/
  flexibility : ℝ
  /-- Channel 7: Sulfur content [0, 0.5, 1] -/
  sulfur : ℝ

/-- Get channel value by index -/
def AAChemistry.channel (chem : AAChemistry) : Fin 8 → ℝ
  | ⟨0, _⟩ => chem.volume
  | ⟨1, _⟩ => chem.charge
  | ⟨2, _⟩ => chem.polarity
  | ⟨3, _⟩ => chem.hDonors
  | ⟨4, _⟩ => chem.hAcceptors
  | ⟨5, _⟩ => chem.aromaticity
  | ⟨6, _⟩ => chem.flexibility
  | ⟨7, _⟩ => chem.sulfur

/-! ## Amino Acid Chemistry Table (Appendix C values) -/

/-- Chemistry encoding for each amino acid (from Appendix C of protein-dec-6.tex)

    Values are normalized to [0,1] or [-1,1] ranges based on:
    - Volume: Normalized by Trp volume (largest)
    - Charge: -1 for Asp/Glu, +1 for Lys/Arg, 0 otherwise
    - Polarity: Dipole moment normalized
    - H-donors/acceptors: Count normalized by max
    - Aromaticity: 1 for Phe/Tyr/Trp/His, 0 otherwise
    - Flexibility: Inverse of steric restriction
    - Sulfur: 1 for Cys, 0.5 for Met, 0 otherwise -/
noncomputable def aaChemistry : AminoAcid → AAChemistry
  -- Small hydrophobic
  | .Ala => ⟨0.15, 0.0, 0.0, 0.0, 0.0, 0.0, 0.9, 0.0⟩
  | .Gly => ⟨0.00, 0.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0⟩  -- Most flexible
  | .Val => ⟨0.35, 0.0, 0.0, 0.0, 0.0, 0.0, 0.4, 0.0⟩
  | .Leu => ⟨0.45, 0.0, 0.0, 0.0, 0.0, 0.0, 0.5, 0.0⟩
  | .Ile => ⟨0.45, 0.0, 0.0, 0.0, 0.0, 0.0, 0.3, 0.0⟩
  -- Proline (special)
  | .Pro => ⟨0.30, 0.0, 0.1, 0.0, 0.0, 0.0, 0.0, 0.0⟩  -- Rigid
  -- Sulfur-containing
  | .Cys => ⟨0.25, 0.0, 0.3, 0.5, 0.5, 0.0, 0.8, 1.0⟩  -- Thiol
  | .Met => ⟨0.45, 0.0, 0.2, 0.0, 0.5, 0.0, 0.7, 0.5⟩  -- Thioether
  -- Aromatic
  | .Phe => ⟨0.65, 0.0, 0.1, 0.0, 0.0, 1.0, 0.4, 0.0⟩
  | .Tyr => ⟨0.70, 0.0, 0.5, 0.5, 0.5, 1.0, 0.4, 0.0⟩
  | .Trp => ⟨1.00, 0.0, 0.4, 0.5, 0.5, 1.0, 0.3, 0.0⟩  -- Largest
  | .His => ⟨0.50, 0.5, 0.7, 0.5, 0.5, 1.0, 0.5, 0.0⟩  -- Partial + charge
  -- Charged (negative)
  | .Asp => ⟨0.35, -1.0, 0.9, 0.0, 1.0, 0.0, 0.7, 0.0⟩
  | .Glu => ⟨0.45, -1.0, 0.9, 0.0, 1.0, 0.0, 0.8, 0.0⟩
  -- Charged (positive)
  | .Lys => ⟨0.50, 1.0, 0.8, 1.0, 0.0, 0.0, 0.9, 0.0⟩
  | .Arg => ⟨0.60, 1.0, 0.9, 1.0, 0.0, 0.0, 0.8, 0.0⟩
  -- Polar uncharged
  | .Asn => ⟨0.35, 0.0, 0.8, 0.5, 1.0, 0.0, 0.7, 0.0⟩
  | .Gln => ⟨0.45, 0.0, 0.8, 0.5, 1.0, 0.0, 0.8, 0.0⟩
  | .Ser => ⟨0.20, 0.0, 0.6, 0.5, 0.5, 0.0, 0.8, 0.0⟩
  | .Thr => ⟨0.30, 0.0, 0.5, 0.5, 0.5, 0.0, 0.6, 0.0⟩

/-! ## Channel Utilities -/

/-- Check if amino acid is aromatic -/
noncomputable def AminoAcid.isAromatic (aa : AminoAcid) : Bool :=
  (aaChemistry aa).aromaticity > 0.5

/-- Check if amino acid is charged -/
noncomputable def AminoAcid.isCharged (aa : AminoAcid) : Bool :=
  let c := (aaChemistry aa).charge
  c > 0.5 ∨ c < -0.5

/-- Check if amino acid is positively charged -/
noncomputable def AminoAcid.isPositive (aa : AminoAcid) : Bool :=
  (aaChemistry aa).charge > 0.5

/-- Check if amino acid is negatively charged -/
noncomputable def AminoAcid.isNegative (aa : AminoAcid) : Bool :=
  (aaChemistry aa).charge < -0.5

/-- Check if amino acid contains sulfur -/
noncomputable def AminoAcid.hasSulfur (aa : AminoAcid) : Bool :=
  (aaChemistry aa).sulfur > 0

/-- Check if amino acid can form disulfide bonds -/
noncomputable def AminoAcid.canDisulfide (aa : AminoAcid) : Bool :=
  (aaChemistry aa).sulfur > 0.9  -- Only Cys

/-! ## Protein Sequence -/

/-- A protein sequence is a list of amino acids -/
abbrev Sequence := List AminoAcid

/-- Sequence length -/
def Sequence.length (s : Sequence) : ℕ := List.length s

/-- Get amino acid at position (with bounds checking) -/
def Sequence.get? (s : Sequence) (i : ℕ) : Option AminoAcid :=
  if h : i < List.length s then
    some (s.get ⟨i, h⟩)
  else
    none

/-- Encode a sequence into chemistry channels -/
noncomputable def Sequence.encode (s : Sequence) : List AAChemistry :=
  s.map aaChemistry

/-- Get channel values across the sequence -/
noncomputable def Sequence.channelProfile (s : Sequence) (c : Fin 8) : List ℝ :=
  (s.encode).map (·.channel c)

/-! ## Chemistry Gates for Contact Scoring -/

/-- Charge compatibility gate for residue pair

    Opposite charges: boost (+1.3)
    Like charges: penalty (×0.7)
    Neutral: no effect (×1.0) -/
noncomputable def chargeGate (chem_i chem_j : AAChemistry) : ℝ :=
  let product := chem_i.charge * chem_j.charge
  if product < -0.5 then 1.3      -- Opposite charges attract
  else if product > 0.5 then 0.7  -- Like charges repel
  else 1.0                         -- Neutral

/-- Hydrogen bond gate for residue pair

    Rewards donor-acceptor complementarity -/
noncomputable def hbondGate (chem_i chem_j : AAChemistry) : ℝ :=
  let don_acc_ij := min chem_i.hDonors chem_j.hAcceptors
  let don_acc_ji := min chem_j.hDonors chem_i.hAcceptors
  1 + 0.15 * don_acc_ij + 0.15 * don_acc_ji

/-- Aromatic interaction gate

    π-stacking between aromatic residues -/
noncomputable def aromaticGate (chem_i chem_j : AAChemistry) : ℝ :=
  if chem_i.aromaticity > 0.5 ∧ chem_j.aromaticity > 0.5
  then 1.2  -- π-stacking bonus
  else 1.0

/-- Sulfur resonance gate for disulfide potential

    High value for Cys-Cys pairs -/
noncomputable def sulfurGate (chem_i chem_j : AAChemistry) : ℝ :=
  chem_i.sulfur * chem_j.sulfur

/-- Combined chemistry gate -/
noncomputable def chemistryGate (chem_i chem_j : AAChemistry) : ℝ :=
  chargeGate chem_i chem_j *
  hbondGate chem_i chem_j *
  aromaticGate chem_i chem_j

end Chemistry
end ProteinFolding
end IndisputableMonolith
