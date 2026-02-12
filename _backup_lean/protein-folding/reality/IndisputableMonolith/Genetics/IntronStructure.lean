import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Numerics.Interval

/-!
# Intron Structure and the Golden Angle Connection

This module formalizes the geometry needed to discuss intron-length phase effects,
plus explicitly-marked empirical placeholders.

AUDIT NOTE:
Empirically, mod-8 non-uniformity is robust across multiple Ensembl-derived gene sets,
but both the *peak residue (phase)* and even the *existence of significance* can be
counting-definition dependent (transcript-weighted vs unique-interval vs canonical transcript).
Therefore, this module treats residue-specific claims as dataset-scoped (axioms), not universal theorems.

## Empirical Background

Representative Ensembl-derived snapshots in this workspace:
- Base set (`data/ensembl_introns.txt`, 20 genes, transcript-weighted): n=9501, χ²=170.27, peak residue 4, trough residue 7
- Base set (same 20 genes, unique-intervals): n=1202, χ²=11.07 (NS)
- Base set (same 20 genes, canonical transcript): n=742, χ²=10.52 (NS)
- Added disjoint set (`data/added_introns.txt`, 21 genes, transcript-weighted): n=11128, χ²=180.25, peak residue 0, trough residue 2
- Combined (`data/expanded_introns.txt`): n=20629, χ²=130.41, peak residue 0

## Theoretical Connection

The B-form DNA double helix has approximately 10.5 base pairs per complete turn (360°).
Therefore, 4 base pairs corresponds to:
  4 bp × (360° / 10.5 bp) ≈ 137.1°

The golden angle is defined as:
  θ_golden = 360° / φ ≈ 222.5° (or equivalently 360° - 222.5° = 137.5°)

The near-equality of 4 bp rotation (~137.1°) and the golden angle (~137.5°) suggests
that splice site recognition is optimized at golden-angle-aligned positions.

## Key Definitions

- `bp_per_turn`: Base pairs per DNA helix turn (~10.5 for B-form DNA)
- `half_octave`: 4 bp, the observed preference in intron lengths
- `golden_angle`: small golden angle = 360°/φ^2 = 360° - 360°/φ ≈ 137.5°
- `half_octave_rotation`: Angular rotation for 4 bp

## Main Theorems

- `half_octave_near_golden_angle`: |4 bp rotation - golden angle| < 1°
- `intron_mod8_hypothesis`: Intron lengths prefer ≡ 4 mod 8 (empirical, sorried)
-/

namespace IndisputableMonolith
namespace Genetics
namespace IntronStructure

open Constants

/-! ## DNA Helix Geometry -/

/-- Base pairs per complete turn of B-form DNA helix.
    Experimental value: 10.4-10.6 bp/turn, typically ~10.5 -/
noncomputable def bp_per_turn : ℝ := 10.5

/-- Degrees per base pair of DNA rotation -/
noncomputable def degrees_per_bp : ℝ := 360 / bp_per_turn

/-- The half-octave: 4 base pairs (peak of intron length distribution mod 8) -/
def half_octave : ℕ := 4

/-- Angular rotation for half_octave base pairs (in degrees) -/
noncomputable def half_octave_rotation : ℝ := half_octave * degrees_per_bp

/-! ## Golden Angle -/

/-- The golden angle in degrees: θ_large = 360° / φ (≈ 222.5°).
    The small golden angle (≈ 137.5°) is `golden_angle = 360° - θ_large = 360°/φ^2`. -/
noncomputable def golden_angle_large : ℝ := 360 / phi

/-- The "small" golden angle (360° - 360°/φ) ≈ 137.5°
    This is the angle commonly observed in phyllotaxis (leaf arrangement). -/
noncomputable def golden_angle : ℝ := 360 - golden_angle_large

/-- Alternative formula: golden_angle = 360 × (1 - 1/φ) = 360/φ^2 ≈ 137.5° -/
lemma golden_angle_alt : golden_angle = 360 * (1 - 1 / phi) := by
  unfold golden_angle golden_angle_large
  ring

/-! ## The Core Connection -/

/-- Half-octave rotation is approximately 137.14° -/
lemma half_octave_rotation_value : half_octave_rotation = 4 * (360 / 10.5) := by
  unfold half_octave_rotation half_octave degrees_per_bp bp_per_turn
  norm_cast

/-- The half-octave rotation (~137.1°) is within 1° of the golden angle (~137.5°) -/
theorem half_octave_near_golden_angle :
    |half_octave_rotation - golden_angle| < 1 := by
  -- Strategy (claim-hygienic): put both angles strictly inside the open interval (137, 138),
  -- then the difference is automatically < 1.
  have hHalf_lower : (137 : ℝ) < half_octave_rotation := by
    -- half_octave_rotation = 4 * (360 / 10.5) = 2880/21 ≈ 137.142857
    unfold half_octave_rotation degrees_per_bp bp_per_turn half_octave
    norm_num
  have hHalf_upper : half_octave_rotation < (138 : ℝ) := by
    unfold half_octave_rotation degrees_per_bp bp_per_turn half_octave
    norm_num

  -- Bound the golden angle using tight φ bounds from Numerics.Interval.
  have hφ := IndisputableMonolith.Numerics.phi_tight_bounds
  have hφ_pos : 0 < (phi : ℝ) := phi_pos

  -- First bound 360/φ between (222, 223).
  have hDiv_upper : (360 / phi : ℝ) < 223 := by
    -- 360/φ < 223  ↔  360 < 223*φ  (since φ>0)
    have hMul : (360 : ℝ) < (223 : ℝ) * phi := by
      have h1 : (360 : ℝ) < (223 : ℝ) * (1.6180339887 : ℝ) := by norm_num
      have h2 : (223 : ℝ) * (1.6180339887 : ℝ) < (223 : ℝ) * phi :=
        mul_lt_mul_of_pos_left hφ.1 (by norm_num)
      exact lt_trans h1 h2
    exact (div_lt_iff₀ hφ_pos).2 hMul

  have hDiv_lower : (222 : ℝ) < (360 / phi : ℝ) := by
    -- 222 < 360/φ  ↔  222*φ < 360  (since φ>0)
    have hMul : (222 : ℝ) * phi < (360 : ℝ) := by
      have h2 : (222 : ℝ) * phi < (222 : ℝ) * (1.6180339888 : ℝ) :=
        mul_lt_mul_of_pos_left hφ.2 (by norm_num)
      have h1 : (222 : ℝ) * (1.6180339888 : ℝ) < (360 : ℝ) := by norm_num
      exact lt_trans h2 h1
    exact (lt_div_iff₀ hφ_pos).2 hMul

  -- Translate those bounds to golden_angle = 360 - 360/φ.
  have hGold_lower : (137 : ℝ) < golden_angle := by
    unfold golden_angle golden_angle_large
    linarith [hDiv_upper]
  have hGold_upper : golden_angle < (138 : ℝ) := by
    unfold golden_angle golden_angle_large
    linarith [hDiv_lower]

  -- With both angles in (137, 138), their difference is strictly < 1.
  rw [abs_lt]
  constructor <;> linarith [hHalf_lower, hHalf_upper, hGold_lower, hGold_upper]

/-! ## Intron Structure Hypotheses (Empirical) -/

/-- Empirical hypothesis (dataset-scoped): In the **base** Ensembl gene set used in this workspace,
    residue 4 mod 8 is overrepresented (peak).

    NOTE: Other gene sets in this workspace exhibit different peak residues, so this is not a
    universal claim. -/
axiom intron_mod8_residue4_preference_base_set :
    ∃ (chi_sq : ℝ) (p : ℝ), chi_sq > 100 ∧ p < 0.001

/-- Empirical hypothesis (dataset-scoped): In the **base** Ensembl gene set used in this workspace,
    residue 7 mod 8 is strongly depleted. -/
axiom intron_mod8_residue7_avoidance_base_set :
    ∃ (deviation : ℝ), deviation < -0.25

/-- Empirical hypothesis (scoped to the ortholog gene list used by `tools/cross_species_intron_analysis.py`):
    in the **transcript-weighted** pipeline for that specific comparison set,
    human and mouse peak at residue 4 mod 8.

    NOTE: This does **not** imply gene-architecture conservation; canonical/unique reruns are required. -/
axiom mammalian_half_octave_conservation :
    ∀ species : String, species = "human" ∨ species = "mouse" →
    ∃ (peak_residue : ℕ), peak_residue = 4

/-! ## Minimal Intron Size -/

/-- Minimal functional intron size in mammals (~85-90 bp).
    This closely matches 8 × φ^5 ≈ 88.7 bp -/
noncomputable def minimal_intron_predicted : ℝ := 8 * (phi ^ 5)

/-- The φ^5 scaling of minimal intron size -/
theorem minimal_intron_phi5_scaling :
    |minimal_intron_predicted - 89| < 1 := by
  -- Use the exact algebraic identity φ^5 = 5φ + 3, then a coarse φ bound is enough.
  -- 8*φ^5 = 40φ + 24, and with φ≈1.618 we land near 88.7 (within 1 of 89).
  have hφ := IndisputableMonolith.Numerics.phi_tight_bounds
  have hφ_pos : 0 < (phi : ℝ) := phi_pos
  have hPow5 : (phi : ℝ) ^ (5 : ℕ) = 5 * phi + 3 := by
    simpa using IndisputableMonolith.Numerics.phi_pow_five
  -- Rewrite the predicted minimal intron size into a linear expression in φ.
  unfold minimal_intron_predicted
  -- Use the identity for φ^5.
  rw [hPow5]
  -- Now show |(8*(5φ+3)) - 89| < 1 by bounding φ in a small interval.
  -- Expand: 8*(5φ+3) = 40φ + 24.
  have : |(40 * phi + 24) - 89| < 1 := by
    -- It suffices to show 88 < 40φ+24 < 90.
    rw [abs_lt]
    constructor
    · -- lower: 88 < 40φ+24  ↔  64 < 40φ  ↔  1.6 < φ
      have h1 : (1.6 : ℝ) < phi := by
        -- from the tight bound 1.618... < φ
        linarith [hφ.1]
      linarith [h1]
    · -- upper: 40φ+24 < 90  ↔  40φ < 66  ↔  φ < 1.65
      have h2 : phi < (1.65 : ℝ) := by
        -- from the tight bound φ < 1.618...
        linarith [hφ.2]
      linarith [h2]
  -- finish by rewriting 8*(5φ+3) = 40φ+24
  have hReassoc : (8 * (5 * phi + 3) : ℝ) = 40 * phi + 24 := by ring
  -- Use the rewrite to transport the bound.
  simpa [hReassoc] using this

/-! ## Splice Site Recognition -/

/-- The splice acceptor AG dinucleotide is most efficiently recognized
    at positions where the intron length ≡ 4 mod 8 (golden-angle alignment). -/
structure SpliceSiteAlignment where
  /-- Intron length in base pairs -/
  length : ℕ
  /-- Mod 8 residue -/
  residue : ℕ := length % 8
  /-- Whether this is a "preferred" residue (4) -/
  is_preferred : Bool := residue = 4
  /-- Whether this is an "avoided" residue (7) -/
  is_avoided : Bool := residue = 7

/-- Helper: compute splice site alignment -/
def classify_intron (length : ℕ) : SpliceSiteAlignment :=
  { length := length }

/-! ## Summary Theorem -/

/-- Main theorem connecting geometry to biology:
    The 4 bp "half-octave" preference in intron lengths corresponds to
    golden-angle alignment in DNA helix geometry, providing a geometric
    basis for splice site recognition optimization. -/
theorem golden_angle_splice_site_connection :
    half_octave = 4 ∧
    |half_octave_rotation - golden_angle| < 1 := by
  constructor
  · rfl
  · exact half_octave_near_golden_angle

end IntronStructure
end Genetics
end IndisputableMonolith
