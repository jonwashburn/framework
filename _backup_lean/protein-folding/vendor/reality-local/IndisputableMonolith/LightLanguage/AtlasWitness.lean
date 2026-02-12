/-
Copyright (c) 2025
Authors: Recognition Science Engineering Team

! This file records the frozen Light Language atlas metadata for Lean.
-/
import Mathlib.Data.List.Basic

namespace LightLanguage

/--
`AtlasWitness` packages the hash-stable metadata exported from the
Light Language discovery tooling (`light-language/synthetic/tokens.json`,
`synthetic/reports/calibration.json`, `synthetic/reports/phi_analysis.json`).

The record exposes:
* `tokenHash` – SHA256 of the frozen dictionary
* `tokenCount` – number of WTokens
* `familyCounts` – coverage counts ordered by the discovery MOVE names
* `coverageMean` – average Boolean coverage across the 13 move families
* `phiPValue`, `phiResidualMean`, `phiHistogram` – φ-locking statistics
* `cConstant`, `phiBandAbs`, `phiBandLog` – calibration constants from the CPM run

These values let Lean theorems reference the empirical atlas without
re-running the Python pipeline.
-/
namespace AtlasWitness

/-- SHA256 hash of `light-language/synthetic/tokens.json`. -/
def tokenHash : String :=
  "c8e2719a32fcd62aeefc876e50eac341ca066820db30c262ebc08b3348dc6012"

/-- Number of WTokens in the frozen dictionary. -/
def tokenCount : Nat := 12

/--
Move-family coverage counts derived from the frozen dictionary.
The order matches `MOVE_NAMES` in the discovery suite.
-/
def familyCounts : List (String × Nat) :=
  [ ("IDENTITY_CHANGE", 0)
  , ("ORDER", 0)
  , ("CONTACT", 2)
  , ("MERGE_SPLIT", 1)
  , ("CROSS_AVOID", 1)
  , ("CLOSURE", 0)
  , ("SYMMETRY", 1)
  , ("GROUPING", 1)
  , ("CONTAINMENT", 0)
  , ("REGISTRATION", 1)
  , ("RHYTHM", 2)
  , ("APPEAR_DECAY", 1)
  , ("BRAID_UNBRAID", 2)
  ]

/-- Families with non-zero coverage. -/
def coveredFamilies : List String :=
  (familyCounts.filter fun entry => entry.snd > 0).map Prod.fst

/-- Families remaining to be populated in the empirical atlas. -/
def missingFamilies : List String :=
  (familyCounts.filter fun entry => entry.snd = 0).map Prod.fst

@[simp] lemma coveredFamilies_length : coveredFamilies.length = 9 := by
  decide

lemma missingFamilies_eq :
    missingFamilies = ["IDENTITY_CHANGE", "ORDER", "CLOSURE", "CONTAINMENT"] := by
  decide

/-- Mean Boolean coverage across the 13 move families. -/
def coverageMean : ℚ := 9 / 13

/-- φ-locking bootstrap p-value. -/
def phiPValue : ℚ := 33 / 1025

/-- Mean residual distance to the φ-lattice. -/
def phiResidualMean : ℚ := 29149 / 305095

/-- φ-residual histogram aggregated by nearest φ-power. -/
def phiHistogram : List (Int × Nat) :=
  [ (-2, 8)
  , (-1, 20)
  , (0, 38)
  ]

/-- CPM coercivity constant `c`. -/
def cConstant : ℚ := 46877 / 674348

/-- Effective absolute φ-band. -/
def phiBandAbs : ℚ := 148164 / 838171

/-- Effective logarithmic φ-band. -/
def phiBandLog : ℚ := 58742 / 537683

/--
Compact record bundling the frozen atlas metadata for downstream proofs.
-/
structure Metadata where
  tokenHash : String
  tokenCount : Nat
  familyCounts : List (String × Nat)
  coverageMean : ℚ
  phiPValue : ℚ
  phiResidualMean : ℚ
  phiHistogram : List (Int × Nat)
  cConstant : ℚ
  phiBandAbs : ℚ
  phiBandLog : ℚ
deriving Repr

/-- Frozen atlas metadata snapshot. -/
def metadata : Metadata :=
  { tokenHash := tokenHash
    tokenCount := tokenCount
    familyCounts := familyCounts
    coverageMean := coverageMean
    phiPValue := phiPValue
    phiResidualMean := phiResidualMean
    phiHistogram := phiHistogram
    cConstant := cConstant
    phiBandAbs := phiBandAbs
    phiBandLog := phiBandLog }

end AtlasWitness

end LightLanguage
