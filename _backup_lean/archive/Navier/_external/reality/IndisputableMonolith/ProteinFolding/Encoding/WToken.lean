import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.ProteinFolding.Encoding.DFT8

/-!
# WToken: Per-Position Recognition Signature

This module defines the WToken structure that encodes the recognition
signature at each position in the protein sequence.

## WToken Components

Each WToken has three components:
1. **k (Dominant Mode)**: Which DFT-8 mode dominates (0-7)
2. **n (φ-Level)**: Quantized amplitude on the φ-ladder (0-3)
3. **τ (Phase)**: Quantized phase within the 8-tick cycle (0-7)

## Physical Interpretation

The WToken is the "recognition fingerprint" of each residue:
- k tells us the structural propensity (helix, strand, coil)
- n tells us the strength of that signal
- τ tells us the phase alignment with the 8-tick cycle

Contact formation requires compatible WTokens: matching modes
and complementary phases create resonance conditions.

-/

namespace IndisputableMonolith
namespace ProteinFolding
namespace WToken

open Constants
open DFT8

/-! ## WToken Structure -/

/-- The WToken recognition signature for a sequence position -/
structure WToken where
  /-- Dominant DFT mode (k ∈ {0..7}) -/
  dominantMode : Fin 8
  /-- φ-ladder level (n ∈ {0..3}) -/
  phiLevel : Fin 4
  /-- Quantized phase (τ ∈ {0..7}) -/
  phase : Fin 8
  deriving DecidableEq, Repr

/-! ## φ-Level Quantization -/

/-- Quantize amplitude to φ-ladder level

    Level 0: amplitude < 1/φ²
    Level 1: 1/φ² ≤ amplitude < 1/φ
    Level 2: 1/φ ≤ amplitude < 1
    Level 3: amplitude ≥ 1 -/
noncomputable def quantizePhiLevel (amplitude : ℝ) : Fin 4 :=
  if amplitude < 1 / phi^2 then ⟨0, by norm_num⟩
  else if amplitude < 1 / phi then ⟨1, by norm_num⟩
  else if amplitude < 1 then ⟨2, by norm_num⟩
  else ⟨3, by norm_num⟩

/-- φ-level boundaries -/
noncomputable def phiLevelBoundary (n : Fin 4) : ℝ :=
  match n with
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1 / phi^2  -- ≈ 0.382
  | ⟨2, _⟩ => 1 / phi    -- ≈ 0.618
  | ⟨3, _⟩ => 1

/-! ## Phase Quantization -/

/-- Quantize continuous phase to 8 discrete values

    Maps [-π, π] to {0, 1, ..., 7} -/
noncomputable def quantizePhase (θ : ℝ) : Fin 8 :=
  let normalized := (θ + Real.pi) / (2 * Real.pi)  -- Map to [0, 1]
  let index := ⌊normalized * 8⌋₊ % 8
  ⟨index, Nat.mod_lt index (by norm_num)⟩

/-- Phase bin center -/
noncomputable def phaseBinCenter (τ : Fin 8) : ℝ :=
  -Real.pi + (τ.val + 0.5) * Real.pi / 4

/-! ## WToken Computation -/

/-- Find dominant mode (argmax of amplitudes) -/
noncomputable def findDominantMode (X : Fin 8 → ℂ) : Fin 8 :=
  -- Find mode with maximum amplitude (excluding DC component)
  let amps : Fin 8 → ℝ := fun k => if k.val = 0 then 0 else amplitude (X k)
  -- Simple argmax (default to mode 2 if all zero)
  if amps ⟨2, by norm_num⟩ ≥ amps ⟨4, by norm_num⟩ ∧
     amps ⟨2, by norm_num⟩ ≥ amps ⟨1, by norm_num⟩ ∧
     amps ⟨2, by norm_num⟩ ≥ amps ⟨3, by norm_num⟩ then ⟨2, by norm_num⟩
  else if amps ⟨4, by norm_num⟩ ≥ amps ⟨1, by norm_num⟩ ∧
          amps ⟨4, by norm_num⟩ ≥ amps ⟨3, by norm_num⟩ then ⟨4, by norm_num⟩
  else if amps ⟨1, by norm_num⟩ ≥ amps ⟨3, by norm_num⟩ then ⟨1, by norm_num⟩
  else ⟨3, by norm_num⟩

/-- Compute WToken from DFT spectrum -/
noncomputable def computeWToken (X : Fin 8 → ℂ) : WToken :=
  let k := findDominantMode X
  let amp := amplitude (X k)
  let ph := phase (X k)
  { dominantMode := k
    phiLevel := quantizePhiLevel amp
    phase := quantizePhase ph }

/-- Compute WToken sequence from sliding DFT -/
noncomputable def computeWTokenSequence (spectra : List (Fin 8 → ℂ)) : List WToken :=
  spectra.map computeWToken

/-! ## WToken Properties -/

/-- Check if WToken indicates helix tendency -/
def WToken.isHelixLike (w : WToken) : Bool :=
  w.dominantMode.val = 2 ∧ w.phiLevel.val ≥ 1

/-- Check if WToken indicates strand tendency -/
def WToken.isStrandLike (w : WToken) : Bool :=
  w.dominantMode.val = 4 ∧ w.phiLevel.val ≥ 1

/-- Check if WToken indicates coil/disordered -/
def WToken.isCoilLike (w : WToken) : Bool :=
  w.phiLevel.val = 0

/-! ## WToken Compatibility for Contacts -/

/-- Mode compatibility between two WTokens

    Same dominant mode increases contact probability -/
def modeCompatible (w1 w2 : WToken) : Bool :=
  w1.dominantMode = w2.dominantMode

/-- Phase complementarity score

    Phases that differ by π/2 (orthogonal) can form stable contacts -/
noncomputable def phaseComplementarity (w1 w2 : WToken) : ℝ :=
  let diff := ((w2.phase.val : ℤ) - (w1.phase.val : ℤ)) % 8
  -- Best complementarity at Δτ = 0 or Δτ = 4
  if diff = 0 ∨ diff = 4 ∨ diff = -4 then 1.0
  else if diff.natAbs = 1 ∨ diff.natAbs = 7 then 0.9
  else if diff.natAbs = 2 ∨ diff.natAbs = 6 then 0.7
  else 0.5

/-- Combined WToken resonance score -/
noncomputable def wtokenResonance (w1 w2 : WToken) : ℝ :=
  let modeScore := if modeCompatible w1 w2 then 1.2 else 1.0
  let phaseScore := phaseComplementarity w1 w2
  let levelSum := (w1.phiLevel.val + w2.phiLevel.val : ℝ)
  let levelFactor := phi ^ (levelSum / 4 - 1)  -- Normalized φ-scaling
  modeScore * phaseScore * levelFactor

/-! ## WToken Summary Statistics -/

/-- Count helix-like WTokens in sequence -/
def countHelixTokens (tokens : List WToken) : ℕ :=
  tokens.filter WToken.isHelixLike |>.length

/-- Count strand-like WTokens in sequence -/
def countStrandTokens (tokens : List WToken) : ℕ :=
  tokens.filter WToken.isStrandLike |>.length

/-- Helix propensity fraction -/
noncomputable def helixFraction (tokens : List WToken) : ℝ :=
  if tokens.isEmpty then 0
  else (countHelixTokens tokens : ℝ) / tokens.length

/-- Strand propensity fraction -/
noncomputable def strandFraction (tokens : List WToken) : ℝ :=
  if tokens.isEmpty then 0
  else (countStrandTokens tokens : ℝ) / tokens.length

end WToken
end ProteinFolding
end IndisputableMonolith
