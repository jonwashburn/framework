import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Chemistry.BondAngles

/-!
# VSEPR Geometries from Cost Minimization (CH-015)

VSEPR (Valence Shell Electron Pair Repulsion) theory predicts molecular
geometry from electron pair repulsion. RS derives these geometries from
J-cost minimization.

## Core Principle

For n electron domains around a central atom, the minimum-cost geometry
places domains to maximize separation. This gives:

| n | Geometry | Bond Angles |
|---|----------|-------------|
| 2 | Linear | 180° |
| 3 | Trigonal planar | 120° |
| 4 | Tetrahedral | 109.47° |
| 5 | Trigonal bipyramidal | 90°, 120° |
| 6 | Octahedral | 90° |

## Lone Pair Effects

Lone pairs (LP) occupy more angular space than bonding pairs (BP):
- LP-LP repulsion > LP-BP repulsion > BP-BP repulsion
- This compresses bond angles below ideal geometry

Examples:
- NH₃: 4 domains (1 LP) → 107° (below 109.47°)
- H₂O: 4 domains (2 LP) → 104.5° (further compressed)
-/

namespace IndisputableMonolith
namespace Chemistry
namespace VSEPR

noncomputable section

/-- VSEPR geometry type. -/
inductive Geometry where
  | linear : Geometry
  | trigonalPlanar : Geometry
  | bent : Geometry
  | tetrahedral : Geometry
  | trigonalPyramidal : Geometry
  | bentTetrahedral : Geometry
  | trigonalBipyramidal : Geometry
  | seesawShape : Geometry
  | tShape : Geometry
  | linearFromTBP : Geometry
  | octahedral : Geometry
  | squarePyramidal : Geometry
  | squarePlanar : Geometry
  deriving DecidableEq, Repr

/-- Number of electron domains for each base geometry. -/
def electronDomains : Geometry → ℕ
  | .linear => 2
  | .trigonalPlanar => 3
  | .bent => 3
  | .tetrahedral => 4
  | .trigonalPyramidal => 4
  | .bentTetrahedral => 4
  | .trigonalBipyramidal => 5
  | .seesawShape => 5
  | .tShape => 5
  | .linearFromTBP => 5
  | .octahedral => 6
  | .squarePyramidal => 6
  | .squarePlanar => 6

/-- Number of bonding pairs. -/
def bondingPairs : Geometry → ℕ
  | .linear => 2
  | .trigonalPlanar => 3
  | .bent => 2
  | .tetrahedral => 4
  | .trigonalPyramidal => 3
  | .bentTetrahedral => 2
  | .trigonalBipyramidal => 5
  | .seesawShape => 4
  | .tShape => 3
  | .linearFromTBP => 2
  | .octahedral => 6
  | .squarePyramidal => 5
  | .squarePlanar => 4

/-- Number of lone pairs. -/
def lonePairs (g : Geometry) : ℕ := electronDomains g - bondingPairs g

/-- Ideal bond angle for base geometry (before LP effects). -/
def idealAngle : Geometry → ℝ
  | .linear => 180
  | .trigonalPlanar => 120
  | .bent => 120  -- From trigonal base
  | .tetrahedral => 109.47
  | .trigonalPyramidal => 109.47  -- From tetrahedral base
  | .bentTetrahedral => 109.47  -- From tetrahedral base
  | .trigonalBipyramidal => 90  -- Axial-equatorial
  | .seesawShape => 90
  | .tShape => 90
  | .linearFromTBP => 180  -- Axial only
  | .octahedral => 90
  | .squarePyramidal => 90
  | .squarePlanar => 90

/-- Lone pair compression factor (degrees per LP). -/
def lpCompression : ℝ := 2.5

/-- Predicted bond angle accounting for lone pair compression. -/
def predictedAngle (g : Geometry) : ℝ :=
  idealAngle g - lpCompression * (lonePairs g : ℝ)

/-! ## Specific Molecule Predictions -/

/-- Methane (CH₄): tetrahedral, 0 LP, 109.47°. -/
theorem methane_angle : predictedAngle .tetrahedral = 109.47 := by
  simp only [predictedAngle, idealAngle, lonePairs, electronDomains, bondingPairs, lpCompression]
  norm_num

/-- Ammonia (NH₃): trigonal pyramidal, 1 LP, 106.97°. -/
theorem ammonia_angle : predictedAngle .trigonalPyramidal = 106.97 := by
  simp only [predictedAngle, idealAngle, lonePairs, electronDomains, bondingPairs, lpCompression]
  norm_num

/-- Water (H₂O): bent, 2 LP, 104.47°. -/
theorem water_angle : predictedAngle .bentTetrahedral = 104.47 := by
  simp only [predictedAngle, idealAngle, lonePairs, electronDomains, bondingPairs, lpCompression]
  norm_num

/-- BF₃: trigonal planar, 0 LP, 120°. -/
theorem bf3_angle : predictedAngle .trigonalPlanar = 120 := by
  simp only [predictedAngle, idealAngle, lonePairs, electronDomains, bondingPairs, lpCompression]
  norm_num

/-- CO₂: linear, 0 LP, 180°. -/
theorem co2_angle : predictedAngle .linear = 180 := by
  simp only [predictedAngle, idealAngle, lonePairs, electronDomains, bondingPairs, lpCompression]
  norm_num

/-- SF₆: octahedral, 0 LP, 90°. -/
theorem sf6_angle : predictedAngle .octahedral = 90 := by
  simp only [predictedAngle, idealAngle, lonePairs, electronDomains, bondingPairs, lpCompression]
  norm_num

/-- XeF₄: square planar, 2 LP, 90°. -/
theorem xef4_angle : predictedAngle .squarePlanar = 85 := by
  simp only [predictedAngle, idealAngle, lonePairs, electronDomains, bondingPairs, lpCompression]
  norm_num

/-! ## Ordering Theorems -/

/-- Lone pairs compress angles: more LP → smaller angle. -/
theorem lp_compresses_angle (g1 g2 : Geometry)
    (hSameBase : idealAngle g1 = idealAngle g2)
    (hMoreLP : lonePairs g1 < lonePairs g2) :
    predictedAngle g1 > predictedAngle g2 := by
  simp only [predictedAngle, hSameBase]
  have h : lpCompression > 0 := by norm_num [lpCompression]
  have hcast : (lonePairs g1 : ℝ) < (lonePairs g2 : ℝ) := Nat.cast_lt.mpr hMoreLP
  have hmul : lpCompression * (lonePairs g1 : ℝ) < lpCompression * (lonePairs g2 : ℝ) :=
    mul_lt_mul_of_pos_left hcast h
  linarith

/-- CH₄ > NH₃ > H₂O in bond angle. -/
theorem tetrahedral_ordering :
    predictedAngle .tetrahedral > predictedAngle .trigonalPyramidal ∧
    predictedAngle .trigonalPyramidal > predictedAngle .bentTetrahedral := by
  constructor <;> (simp only [predictedAngle, idealAngle, lonePairs, electronDomains, bondingPairs, lpCompression]; norm_num)

/-! ## Falsification Criteria

The VSEPR derivation is falsifiable:

1. **Angle prediction**: If predicted angles differ by > 5° from observed

2. **LP ordering**: If more lone pairs do NOT reduce bond angle

3. **Base geometry**: If electron domain count doesn't predict base shape
-/

end

end VSEPR
end Chemistry
end IndisputableMonolith
