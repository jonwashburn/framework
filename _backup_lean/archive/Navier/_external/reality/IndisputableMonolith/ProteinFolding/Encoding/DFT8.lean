import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.ProteinFolding.Encoding.Chemistry

/-!
# DFT-8 Transform for Sequence Analysis

This module implements the 8-point Discrete Fourier Transform aligned with
the 8-beat recognition cycle.

## Key Concepts

- **DFT-8**: 8-point transform extracting frequency content from sliding windows
- **Mode 2**: Helical periodicity signal (α-helix has ~3.6 residue period)
- **Mode 4**: Strand alternation signal (β-strand has ~2 residue period)
- **Mode Interpretation**: DFT modes map to secondary structure propensities

## Physical Motivation

The 8-point window size matches the 8-tick cycle of the recognition ledger.
This synchronization allows the DFT modes to directly correspond to the
coherence patterns that stabilize secondary structures.

-/

namespace IndisputableMonolith
namespace ProteinFolding
namespace DFT8

open Constants
open Chemistry

/-! ## Complex Number Utilities -/

/-- The 8th root of unity: ω = e^(-2πi/8) -/
noncomputable def omega : ℂ := Complex.exp (-2 * Real.pi * Complex.I / 8)

/-- ω^8 = 1 (fundamental periodicity) -/
theorem omega_pow_8 : omega ^ 8 = 1 := by
  simp only [omega]
  rw [← Complex.exp_nat_mul]
  simp only [Nat.cast_ofNat]
  ring_nf
  rw [mul_comm, ← mul_assoc, ← mul_assoc]
  simp only [mul_div_assoc, div_self (by norm_num : (8 : ℂ) ≠ 0)]
  rw [mul_one, mul_comm Real.pi _, ← mul_assoc]
  simp only [neg_mul, mul_neg]
  rw [show (-(2 : ℂ) * Complex.I * ↑Real.pi) = Complex.I * (-(2 * Real.pi)) by ring]
  rw [Complex.exp_mul_I]
  simp only [Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [Complex.cos_neg, Complex.sin_neg]
  simp [Real.cos_two_pi, Real.sin_two_pi]

/-! ## DFT-8 Transform -/

/-- 8-point DFT of a signal -/
noncomputable def dft8 (x : Fin 8 → ℂ) : Fin 8 → ℂ := fun k =>
  ∑ n : Fin 8, x n * omega ^ (n.val * k.val)

/-- Inverse DFT-8 -/
noncomputable def idft8 (X : Fin 8 → ℂ) : Fin 8 → ℂ := fun n =>
  (1 / 8) * ∑ k : Fin 8, X k * (Complex.exp (2 * Real.pi * Complex.I / 8)) ^ (n.val * k.val)

/-- DFT-8 of a real-valued signal -/
noncomputable def dft8Real (x : Fin 8 → ℝ) : Fin 8 → ℂ :=
  dft8 (fun n => (x n : ℂ))

/-! ## Amplitude and Phase Extraction -/

/-- Amplitude (magnitude) of a complex number -/
noncomputable def amplitude (z : ℂ) : ℝ := Complex.abs z

/-- Phase (argument) of a complex number -/
noncomputable def phase (z : ℂ) : ℝ := Complex.arg z

/-- Extract mode amplitudes from DFT -/
noncomputable def modeAmplitudes (X : Fin 8 → ℂ) : Fin 8 → ℝ := fun k =>
  amplitude (X k)

/-- Extract mode phases from DFT -/
noncomputable def modePhases (X : Fin 8 → ℂ) : Fin 8 → ℝ := fun k =>
  phase (X k)

/-- Power at each mode -/
noncomputable def modePower (X : Fin 8 → ℂ) : Fin 8 → ℝ := fun k =>
  (amplitude (X k)) ^ 2

/-! ## Sliding Window DFT -/

/-- Extract 8-element window from a sequence at position i -/
def extractWindow (signal : List ℝ) (i : ℕ) : Fin 8 → ℝ := fun k =>
  (signal.get? (i + k.val)).getD 0

/-- Sliding DFT-8 across a sequence -/
noncomputable def slidingDFT8 (signal : List ℝ) : List (Fin 8 → ℂ) :=
  if signal.length < 8 then []
  else List.map (fun i => dft8Real (extractWindow signal i))
                (List.range (signal.length - 7))

/-! ## Mode Interpretation for Secondary Structure -/

/-- Mode 2 corresponds to helical periodicity (~3.6 residues/turn)

    High Mode 2 amplitude indicates helix-forming tendency -/
def mode2 : Fin 8 := ⟨2, by norm_num⟩

/-- Mode 4 corresponds to strand alternation (2-residue period)

    High Mode 4 amplitude indicates strand-forming tendency -/
def mode4 : Fin 8 := ⟨4, by norm_num⟩

/-- Mode 0 is the DC component (average) -/
def mode0 : Fin 8 := ⟨0, by norm_num⟩

/-- Helix signal strength from DFT -/
noncomputable def helixSignal (X : Fin 8 → ℂ) : ℝ :=
  Real.sqrt (modePower X mode2 / 8)

/-- Strand signal strength from DFT -/
noncomputable def strandSignal (X : Fin 8 → ℂ) : ℝ :=
  Real.sqrt (modePower X mode4 / 8)

/-- Mode 2/Mode 4 ratio for secondary structure classification

    Ratio > 1.6: predominantly α-helical
    Ratio < 1.1: predominantly β-sheet
    Otherwise: mixed α/β -/
noncomputable def m2m4Ratio (X : Fin 8 → ℂ) : ℝ :=
  let p2 := modePower X mode2
  let p4 := modePower X mode4
  if p4 > 0.001 then p2 / p4 else 10  -- Avoid division by zero

/-! ## Sector Classification -/

/-- Fold sector classification based on DFT analysis -/
inductive FoldSector
  | AlphaBundle   -- Predominantly α-helical
  | BetaSheet     -- Predominantly β-sheet
  | AlphaBeta     -- Mixed α/β
  | Disordered    -- No clear secondary structure
  deriving DecidableEq, Repr

/-- Classify fold sector from M2/M4 ratio -/
noncomputable def classifySector (X : Fin 8 → ℂ) : FoldSector :=
  let ratio := m2m4Ratio X
  let p2 := modePower X mode2
  let p4 := modePower X mode4
  if p2 + p4 < 0.1 then FoldSector.Disordered
  else if ratio > 1.6 then FoldSector.AlphaBundle
  else if ratio < 1.1 then FoldSector.BetaSheet
  else FoldSector.AlphaBeta

/-! ## Sequence-Level DFT Analysis -/

/-- Compute average DFT spectrum for a sequence channel -/
noncomputable def averageSpectrum (signal : List ℝ) : Fin 8 → ℝ := fun k =>
  let spectra := slidingDFT8 signal
  if spectra.isEmpty then 0
  else (spectra.map (fun X => amplitude (X k))).sum / spectra.length

/-- Total power at Mode 2 across sequence -/
noncomputable def totalMode2Power (signal : List ℝ) : ℝ :=
  let spectra := slidingDFT8 signal
  (spectra.map (fun X => modePower X mode2)).sum

/-- Total power at Mode 4 across sequence -/
noncomputable def totalMode4Power (signal : List ℝ) : ℝ :=
  let spectra := slidingDFT8 signal
  (spectra.map (fun X => modePower X mode4)).sum

/-- Overall sequence sector from integrated DFT analysis -/
noncomputable def sequenceSector (signal : List ℝ) : FoldSector :=
  let p2 := totalMode2Power signal
  let p4 := totalMode4Power signal
  if p2 + p4 < 0.1 then FoldSector.Disordered
  else if p4 > 0.001 ∧ p2 / p4 > 1.6 then FoldSector.AlphaBundle
  else if p2 > 0.001 ∧ p4 / p2 > 0.9 then FoldSector.BetaSheet
  else FoldSector.AlphaBeta

/-! ## Phase Coherence -/

/-- Phase difference between two positions at a given mode -/
noncomputable def phaseDiff (X_i X_j : Fin 8 → ℂ) (mode : Fin 8) : ℝ :=
  let φ_i := phase (X_i mode)
  let φ_j := phase (X_j mode)
  -- Normalize to [-π, π]
  let diff := φ_j - φ_i
  if diff > Real.pi then diff - 2 * Real.pi
  else if diff < -Real.pi then diff + 2 * Real.pi
  else diff

/-- Phase coherence score (cos of phase difference) -/
noncomputable def phaseCoherence (X_i X_j : Fin 8 → ℂ) (mode : Fin 8) : ℝ :=
  Real.cos (phaseDiff X_i X_j mode)

end DFT8
end ProteinFolding
end IndisputableMonolith
