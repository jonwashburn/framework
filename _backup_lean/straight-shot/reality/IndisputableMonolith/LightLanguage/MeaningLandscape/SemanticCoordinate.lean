import Mathlib
import IndisputableMonolith.Water.WTokenIso
import IndisputableMonolith.Token.WTokenId
import IndisputableMonolith.Constants

/-!
# Semantic Coordinates for WTokens

This module defines the **intrinsic semantic coordinate system** for WTokens.
The coordinate tuple contains NO English labels — it is purely mathematical.

## Main Definitions

* `GaugeClass` — Phase/gauge equivalence class (real, imaginary, mixed)
* `ConjugatePair` — DFT mode conjugate pairing structure
* `OperatorClass` — Primary LNAL operator affinity
* `SemanticCoordinate` — Complete intrinsic identity tuple
* `toSemanticCoordinate` — Conversion from WTokenId

## Design Principle

English labels (e.g., "Origin", "Harmony") are **display-only UI**.
All proofs and structural reasoning should use `SemanticCoordinate`.

## Key Theorems

* `toSemanticCoordinate_injective` — Distinct tokens have distinct coordinates
* `semanticCoordinate_card_eq_20` — Exactly 20 valid coordinate tuples

-/

namespace IndisputableMonolith
namespace LightLanguage
namespace MeaningLandscape

open Water Token Constants

/-! ## Gauge Class -/

/-- Phase/gauge equivalence class for DFT modes.
    - `real`: Mode patterns with zero imaginary component at t=0
    - `imaginary`: Mode patterns with zero real component at t=0
    - `mixed`: Modes with both real and imaginary components -/
inductive GaugeClass : Type
  | real       -- τ₀ offset: cosine-like
  | imaginary  -- τ₂ offset: sine-like
  | mixed      -- General complex: modes 1-3, 5-7
deriving DecidableEq, Repr, Hashable

instance : Fintype GaugeClass where
  elems := {.real, .imaginary, .mixed}
  complete := fun x => by cases x <;> simp

/-! ## Conjugate Pair Structure -/

/-- Conjugate pairing structure for DFT modes.
    Mode k pairs with mode (8-k) to form complex conjugates.
    Mode 4 is self-conjugate (Nyquist). -/
inductive ConjugatePair : Type
  | pair_1_7   -- Modes 1 and 7 are conjugates
  | pair_2_6   -- Modes 2 and 6 are conjugates
  | pair_3_5   -- Modes 3 and 5 are conjugates
  | self_4     -- Mode 4 is self-conjugate (Nyquist frequency)
deriving DecidableEq, Repr, Hashable

instance : Fintype ConjugatePair where
  elems := {.pair_1_7, .pair_2_6, .pair_3_5, .self_4}
  complete := fun x => by cases x <;> simp

/-- Map WTokenMode to its conjugate pair -/
def modeToConjugatePair : WTokenMode → ConjugatePair
  | .mode1_7 => .pair_1_7
  | .mode2_6 => .pair_2_6
  | .mode3_5 => .pair_3_5
  | .mode4   => .self_4

/-! ## Operator Class -/

/-- Primary LNAL operator affinity for each mode family.
    This captures which operation a token "naturally" invokes. -/
inductive OperatorClass : Type
  | lock    -- Structural: establishes stable patterns (mode 1+7)
  | braid   -- Relational: weaves connections (mode 2+6)
  | fold    -- Transformational: changes state (mode 3+5)
  | merge   -- Integrative: combines/unifies (mode 4)
deriving DecidableEq, Repr, Hashable

instance : Fintype OperatorClass where
  elems := {.lock, .braid, .fold, .merge}
  complete := fun x => by cases x <;> simp

/-- Map WTokenMode to its primary operator class -/
def modeToOperatorClass : WTokenMode → OperatorClass
  | .mode1_7 => .lock
  | .mode2_6 => .braid
  | .mode3_5 => .fold
  | .mode4   => .merge

/-! ## Semantic Coordinate -/

/-- Complete intrinsic identity of a semantic atom.

    This tuple contains NO English labels — it is purely mathematical.
    All structural reasoning should use this representation.

    The 20 WTokens arise from:
    - 4 mode families × 4 φ-levels = 16 tokens (modes 1-3 have τ₀ only)
    - mode 4 × 4 φ-levels × 2 τ-offsets = 8 tokens
    - But mode 4 with τ₀ already counted above, so: 16 + 4 = 20 -/
structure SemanticCoordinate where
  /-- Primary DFT mode family -/
  modeFamily : WTokenMode
  /-- φ-amplitude level (0..3) -/
  phiLevel : PhiLevel
  /-- τ-offset (only mode4 can have tau2) -/
  tauOffset : TauOffset
  /-- Validity: non-mode4 tokens must have tau0 -/
  tau_valid : modeFamily ≠ WTokenMode.mode4 → tauOffset = TauOffset.tau0 := by decide
deriving Repr

/-- Two semantic coordinates are equal iff all fields match -/
instance : DecidableEq SemanticCoordinate := fun a b =>
  if h1 : a.modeFamily = b.modeFamily then
    if h2 : a.phiLevel = b.phiLevel then
      if h3 : a.tauOffset = b.tauOffset then
        isTrue (by cases a; cases b; simp_all)
      else isFalse (by intro h; cases h; exact h3 rfl)
    else isFalse (by intro h; cases h; exact h2 rfl)
  else isFalse (by intro h; cases h; exact h1 rfl)

/-! ## Derived Properties -/

/-- Conjugate pairing structure -/
def SemanticCoordinate.conjugatePair (s : SemanticCoordinate) : ConjugatePair :=
  modeToConjugatePair s.modeFamily

/-- Primary operator class -/
def SemanticCoordinate.operatorClass (s : SemanticCoordinate) : OperatorClass :=
  modeToOperatorClass s.modeFamily

/-- Gauge class based on mode and τ-offset -/
def SemanticCoordinate.gaugeClass (s : SemanticCoordinate) : GaugeClass :=
  match s.modeFamily, s.tauOffset with
  | .mode4, .tau0 => .real
  | .mode4, .tau2 => .imaginary
  | _, _ => .mixed  -- Non-mode4 are general complex

/-- Characteristic frequency (Hz) based on mode number × base frequency.
    Base frequency = 5 Hz (40 Hz / 8 ticks). -/
noncomputable def SemanticCoordinate.frequency (s : SemanticCoordinate) : ℝ :=
  let baseFreq : ℝ := 5  -- Hz
  let modeNumber : ℕ := match s.modeFamily with
    | .mode1_7 => 1  -- Primary mode of the conjugate pair
    | .mode2_6 => 2
    | .mode3_5 => 3
    | .mode4   => 4
  baseFreq * modeNumber

/-- Amplitude scaling factor based on φ-level: φⁿ -/
noncomputable def SemanticCoordinate.amplitude (s : SemanticCoordinate) : ℝ :=
  let n : ℕ := phiLevelToNat s.phiLevel
  phi ^ n

/-- Energy contribution: amplitude² -/
noncomputable def SemanticCoordinate.energyContribution (s : SemanticCoordinate) : ℝ :=
  s.amplitude ^ 2

/-- Symmetry order (number of distinct phase states in one cycle) -/
def SemanticCoordinate.symmetryOrder (s : SemanticCoordinate) : ℕ :=
  match s.modeFamily with
  | .mode1_7 => 8  -- Period 8
  | .mode2_6 => 4  -- Period 4
  | .mode3_5 => 8  -- Period 8 (with different phase)
  | .mode4   => 2  -- Period 2 (Nyquist)

/-! ## Conversion from WTokenSpec -/

/-- Convert WTokenSpec to SemanticCoordinate -/
def specToCoordinate (w : WTokenSpec) : SemanticCoordinate where
  modeFamily := w.mode
  phiLevel := w.phi_level
  tauOffset := w.tau_offset
  tau_valid := w.tau_valid

/-- Convert SemanticCoordinate back to WTokenSpec -/
def SemanticCoordinate.toWTokenSpec (s : SemanticCoordinate) : WTokenSpec where
  mode := s.modeFamily
  phi_level := s.phiLevel
  tau_offset := s.tauOffset
  tau_valid := s.tau_valid

/-- Roundtrip: WTokenSpec → SemanticCoordinate → WTokenSpec is identity -/
@[simp] theorem spec_roundtrip (w : WTokenSpec) :
    (specToCoordinate w).toWTokenSpec = w := by
  cases w
  simp only [specToCoordinate, SemanticCoordinate.toWTokenSpec, WTokenSpec.mk.injEq, and_self]

/-- Roundtrip: SemanticCoordinate → WTokenSpec → SemanticCoordinate is identity -/
@[simp] theorem SemanticCoordinate.roundtrip (s : SemanticCoordinate) :
    specToCoordinate s.toWTokenSpec = s := by
  cases s
  simp only [specToCoordinate, SemanticCoordinate.toWTokenSpec, SemanticCoordinate.mk.injEq,
    and_self]

/-! ## Conversion from WTokenId -/

/-- Convert WTokenId to SemanticCoordinate -/
def idToCoordinate (w : WTokenId) : SemanticCoordinate :=
  specToCoordinate (WTokenId.toSpec w)

/-- Distinct WTokenIds produce distinct SemanticCoordinates -/
theorem idToCoordinate_injective :
    Function.Injective idToCoordinate := by
  intro w1 w2 h
  -- Use decidability: both types are finite
  cases w1 <;> cases w2 <;> first | rfl | (simp only [idToCoordinate, specToCoordinate] at h; contradiction)

/-! ## Enumeration -/

/-- Generate all valid SemanticCoordinates -/
def allSemanticCoordinates : List SemanticCoordinate :=
  let modes := [WTokenMode.mode1_7, WTokenMode.mode2_6, WTokenMode.mode3_5, WTokenMode.mode4]
  let levels := [PhiLevel.level0, PhiLevel.level1, PhiLevel.level2, PhiLevel.level3]
  let taus := [TauOffset.tau0, TauOffset.tau2]
  modes.flatMap fun m =>
    levels.flatMap fun l =>
      taus.filterMap fun t =>
        if h : m ≠ WTokenMode.mode4 → t = TauOffset.tau0 then
          some ⟨m, l, t, h⟩
        else
          none

/-- There are exactly 20 semantic coordinates -/
theorem semanticCoordinate_count : allSemanticCoordinates.length = 20 := by
  native_decide

/-- Every WTokenId maps to a coordinate in the enumeration -/
theorem idToCoordinate_complete (w : WTokenId) :
    idToCoordinate w ∈ allSemanticCoordinates := by
  -- The enumeration covers all valid combinations
  simp only [allSemanticCoordinates, idToCoordinate, specToCoordinate]
  cases w <;> native_decide

/-! ## Display Label (UI Only) -/

/-- Display label for UI purposes ONLY.

    **WARNING**: This function is for human-readable output only.
    DO NOT use in proofs or structural reasoning.
    Use `SemanticCoordinate` for all formal work. -/
def SemanticCoordinate.displayLabel (s : SemanticCoordinate) : String :=
  let modeStr := match s.modeFamily with
    | .mode1_7 => "M1"
    | .mode2_6 => "M2"
    | .mode3_5 => "M3"
    | .mode4   => "M4"
  let phiStr := match s.phiLevel with
    | .level0 => "φ⁰"
    | .level1 => "φ¹"
    | .level2 => "φ²"
    | .level3 => "φ³"
  let tauStr := match s.tauOffset with
    | .tau0 => "τ₀"
    | .tau2 => "τ₂"
  s!"{modeStr}-{phiStr}-{tauStr}"

/-! ## Summary Report -/

/-- Generate a summary of all semantic coordinates -/
def semanticCoordinateSummary : String :=
  let header := "╔════════════════════════════════════════════════════════════════╗\n" ++
                "║           SEMANTIC COORDINATE SYSTEM                          ║\n" ++
                "╠════════════════════════════════════════════════════════════════╣\n"
  let body := "║ Total coordinates: 20                                         ║\n" ++
              "║                                                                ║\n" ++
              "║ Mode families: 4 (M1, M2, M3, M4)                              ║\n" ++
              "║ φ-levels: 4 (φ⁰, φ¹, φ², φ³)                                   ║\n" ++
              "║ τ-offsets: 2 (τ₀, τ₂) — only M4 uses τ₂                        ║\n" ++
              "║                                                                ║\n" ++
              "║ Structure:                                                     ║\n" ++
              "║   M1 (lock):  4 tokens (φ⁰-φ³ × τ₀)                            ║\n" ++
              "║   M2 (braid): 4 tokens (φ⁰-φ³ × τ₀)                            ║\n" ++
              "║   M3 (fold):  4 tokens (φ⁰-φ³ × τ₀)                            ║\n" ++
              "║   M4 (merge): 8 tokens (φ⁰-φ³ × {τ₀, τ₂})                      ║\n" ++
              "║                                                                ║\n" ++
              "║ Derived properties:                                            ║\n" ++
              "║   • frequency: mode × 5 Hz                                     ║\n" ++
              "║   • amplitude: φⁿ                                              ║\n" ++
              "║   • energy: φ²ⁿ                                                ║\n" ++
              "║   • symmetryOrder: 8/4/8/2 by mode                             ║\n"
  let footer := "╚════════════════════════════════════════════════════════════════╝"
  header ++ body ++ footer

#eval semanticCoordinateSummary

end MeaningLandscape
end LightLanguage
end IndisputableMonolith
