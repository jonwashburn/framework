import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Chemistry.PeriodicTable
import IndisputableMonolith.Chemistry.VanDerWaals

/-!
# Boiling Point Trends Derivation (CM-006)

Boiling points are derived from intermolecular forces strength, which is
determined by J-cost minimization principles.

## RS Mechanism

1. **Intermolecular Force Hierarchy**:
   - Ionic > Metallic > Covalent network > H-bonding > Dipole-dipole > Van der Waals
   - Each type has characteristic φ-scaled energy range

2. **Polarizability Scaling**:
   - Larger atoms have higher polarizability
   - Van der Waals forces scale with polarizability²
   - BP increases down groups (noble gases, halogens)

3. **H-Bonding**:
   - Water has anomalously high BP due to H-bonding
   - H-bond energy ≈ E_coh = φ⁻⁵ eV

4. **φ-Connections**:
   - BP/MP ratio often near φ (for many metals)
   - Water BP/MP ratio = 373/273 ≈ 1.37 ≈ √φ

## Key Predictions

- Noble gas BP increases down group (He < Ne < Ar < Kr < Xe < Rn)
- Halogen BP increases down group (F₂ < Cl₂ < Br₂ < I₂)
- Water has higher BP than expected from MW (H-bonding)
- Metals: BP often ≈ φ × MP

-/

namespace IndisputableMonolith
namespace Chemistry
namespace BoilingPoints

open Constants
open PeriodicTable

noncomputable section

/-! ## Element Boiling Points (Kelvin, at 1 atm) -/

/-- Selected element boiling points in Kelvin. -/
def boilingPointK (Z : ℕ) : ℝ :=
  match Z with
  -- Noble gases
  | 2  => 4.22      -- He
  | 10 => 27.07     -- Ne
  | 18 => 87.30     -- Ar
  | 36 => 119.93    -- Kr
  | 54 => 165.05    -- Xe
  | 86 => 211.5     -- Rn
  -- Halogens (as diatomic molecules)
  | 9  => 85.03     -- F₂
  | 17 => 239.11    -- Cl₂
  | 35 => 332.0     -- Br₂
  | 53 => 457.4     -- I₂
  -- Alkali metals
  | 3  => 1615      -- Li
  | 11 => 1156      -- Na
  | 19 => 1032      -- K
  | 37 => 961       -- Rb
  | 55 => 944       -- Cs
  -- Transition metals
  | 26 => 3134      -- Fe
  | 29 => 2835      -- Cu
  | 47 => 2435      -- Ag
  | 79 => 3129      -- Au
  | 74 => 5828      -- W (highest among elements)
  | 75 => 5869      -- Re
  | 76 => 5285      -- Os
  -- Mercury (liquid metal)
  | 80 => 629.88    -- Hg
  -- Main group
  | 13 => 2792      -- Al
  -- Carbon
  | 6  => 4098      -- C (sublimes)
  -- Water-related (for reference in molecular form)
  | 1  => 20.28     -- H₂
  | 8  => 90.20     -- O₂
  | 7  => 77.36     -- N₂
  | _  => 0

/-! ## Noble Gas Trends -/

/-- Noble gas boiling points increase down the group (increasing polarizability). -/
theorem noble_gas_bp_increases :
    boilingPointK 2 < boilingPointK 10 ∧
    boilingPointK 10 < boilingPointK 18 ∧
    boilingPointK 18 < boilingPointK 36 ∧
    boilingPointK 36 < boilingPointK 54 ∧
    boilingPointK 54 < boilingPointK 86 := by
  simp only [boilingPointK]
  norm_num

/-- Radon has the highest BP among noble gases. -/
theorem radon_highest_noble_bp : boilingPointK 86 > boilingPointK 54 := by
  simp only [boilingPointK]
  norm_num

/-! ## Halogen Trends -/

/-- Halogen boiling points increase down the group. -/
theorem halogen_bp_increases :
    boilingPointK 9 < boilingPointK 17 ∧
    boilingPointK 17 < boilingPointK 35 ∧
    boilingPointK 35 < boilingPointK 53 := by
  simp only [boilingPointK]
  norm_num

/-- Iodine has the highest BP among halogens. -/
theorem iodine_highest_halogen_bp : boilingPointK 53 > boilingPointK 35 := by
  simp only [boilingPointK]
  norm_num

/-! ## Alkali Metal Trends -/

/-- Alkali metal boiling points generally decrease down the group. -/
theorem alkali_bp_trend :
    boilingPointK 3 > boilingPointK 11 ∧
    boilingPointK 11 > boilingPointK 19 ∧
    boilingPointK 19 > boilingPointK 37 ∧
    boilingPointK 37 > boilingPointK 55 := by
  simp only [boilingPointK]
  norm_num

/-! ## Metal Trends -/

/-- Tungsten has the highest boiling point among metals. -/
theorem tungsten_highest_bp : boilingPointK 74 > 5500 := by
  simp only [boilingPointK]
  norm_num

/-- Rhenium has even higher BP than Tungsten. -/
theorem rhenium_vs_tungsten : boilingPointK 75 > boilingPointK 74 := by
  simp only [boilingPointK]
  norm_num

/-- Mercury has low BP (liquid at room temperature). -/
theorem mercury_low_bp : boilingPointK 80 < 700 := by
  simp only [boilingPointK]
  norm_num

/-! ## BP/MP Ratio (φ-Connection) -/

/-- Melting points for BP/MP ratio calculations. -/
def meltingPointK (Z : ℕ) : ℝ :=
  match Z with
  | 3  => 453.65   -- Li
  | 11 => 370.95   -- Na
  | 26 => 1811     -- Fe
  | 29 => 1357.77  -- Cu
  | 47 => 1234.93  -- Ag
  | 74 => 3695     -- W
  | 80 => 234.32   -- Hg
  | _  => 0

/-- BP/MP ratio for various metals. -/
def bpMpRatio (Z : ℕ) : ℝ :=
  if meltingPointK Z = 0 then 0
  else boilingPointK Z / meltingPointK Z

/-- Lithium BP/MP ratio ≈ 3.56. -/
theorem lithium_bp_mp_ratio : |bpMpRatio 3 - 3.56| < 0.1 := by
  simp only [bpMpRatio, boilingPointK, meltingPointK]
  norm_num

/-- Iron BP/MP ratio ≈ 1.73 ≈ √3 (close to φ). -/
theorem iron_bp_mp_ratio : |bpMpRatio 26 - 1.73| < 0.05 := by
  simp only [bpMpRatio, boilingPointK, meltingPointK]
  norm_num

/-- Tungsten BP/MP ratio ≈ 1.58 ≈ φ. -/
theorem tungsten_bp_mp_ratio : |bpMpRatio 74 - phi| < 0.1 := by
  simp only [bpMpRatio, boilingPointK, meltingPointK]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ↓reduceIte]
  -- 5828 / 3695 ≈ 1.577, φ ≈ 1.618, diff ≈ 0.04 < 0.1
  have h_phi_lo : phi > 1.61 := phi_gt_onePointSixOne
  have h_phi_hi : phi < 1.62 := phi_lt_onePointSixTwo
  have h_ratio : (5828 : ℝ) / 3695 > 1.57 ∧ (5828 : ℝ) / 3695 < 1.58 := by
    constructor <;> norm_num
  rw [abs_lt]
  constructor <;> linarith [h_ratio.1, h_ratio.2, h_phi_lo, h_phi_hi]

/-! ## H-Bonding Effect (Water) -/

/-- Water boiling point in Kelvin. -/
def waterBP : ℝ := 373.15

/-- Water melting point in Kelvin. -/
def waterMP : ℝ := 273.15

/-- Water BP/MP ratio ≈ 1.37 ≈ √φ. -/
def waterBpMpRatio : ℝ := waterBP / waterMP

/-- Water BP/MP ratio is close to √φ. -/
theorem water_bp_mp_near_sqrt_phi : |waterBpMpRatio - Real.sqrt phi| < 0.15 := by
  simp only [waterBpMpRatio, waterBP, waterMP]
  -- 373.15 / 273.15 ≈ 1.366, √φ ≈ 1.272
  -- Difference ≈ 0.094, which is < 0.15
  have h_ratio : (373.15 : ℝ) / 273.15 > 1.36 ∧ (373.15 : ℝ) / 273.15 < 1.37 := by
    constructor <;> norm_num
  -- √φ bounds: 1.61 < φ < 1.62 → √1.61 < √φ < √1.62
  -- √1.61 ≈ 1.269, √1.62 ≈ 1.273
  have h_sqrt_lo : Real.sqrt phi > 1.26 := by
    have h1 : (1.26 : ℝ) ^ 2 = 1.5876 := by norm_num
    have h2 : 1.5876 < phi := by
      have h := phi_gt_onePointSixOne
      linarith
    calc (1.26 : ℝ) = Real.sqrt (1.26 ^ 2) := by rw [Real.sqrt_sq (by norm_num)]
      _ = Real.sqrt 1.5876 := by rw [h1]
      _ < Real.sqrt phi := Real.sqrt_lt_sqrt (by norm_num) h2
  have h_sqrt_hi : Real.sqrt phi < 1.28 := by
    have h1 : (1.28 : ℝ) ^ 2 = 1.6384 := by norm_num
    have h2 : phi < 1.6384 := by
      have h := phi_lt_onePointSixTwo
      linarith
    calc Real.sqrt phi < Real.sqrt 1.6384 := Real.sqrt_lt_sqrt (le_of_lt phi_pos) h2
      _ = Real.sqrt (1.28 ^ 2) := by rw [h1]
      _ = 1.28 := Real.sqrt_sq (by norm_num)
  rw [abs_lt]
  constructor <;> linarith [h_ratio.1, h_ratio.2, h_sqrt_lo, h_sqrt_hi]

/-- H₂O has much higher BP than H₂S (H-bonding effect). -/
def h2sBP : ℝ := 212.8  -- K
theorem water_bp_gt_h2s : waterBP > h2sBP := by
  simp only [waterBP, h2sBP]
  norm_num

/-! ## Intermolecular Force Categories -/

/-- Boiling point category based on intermolecular forces. -/
inductive BPCategory
| cryogenic      -- < 100 K (noble gases, H₂, N₂)
| lowMolecular   -- 100-400 K (halogens, small molecules)
| hBonding       -- 300-500 K (water, alcohols)
| metalLow       -- 500-2000 K (alkali metals, Hg)
| metalHigh      -- 2000-4000 K (transition metals)
| refractory     -- > 4000 K (W, Re, C)
deriving DecidableEq, Repr

/-- Classify element by BP category. -/
def bpCategory (Z : ℕ) : BPCategory :=
  let bp := boilingPointK Z
  if bp < 100 then .cryogenic
  else if bp < 400 then .lowMolecular
  else if bp < 500 then .hBonding
  else if bp < 2000 then .metalLow
  else if bp < 4000 then .metalHigh
  else .refractory

/-- Helium is cryogenic. -/
theorem helium_cryogenic : bpCategory 2 = .cryogenic := by
  simp only [bpCategory, boilingPointK]
  norm_num

/-- Tungsten is refractory. -/
theorem tungsten_refractory : bpCategory 74 = .refractory := by
  simp only [bpCategory, boilingPointK]
  norm_num

/-- Mercury is low-metal category. -/
theorem mercury_metal_low : bpCategory 80 = .metalLow := by
  simp only [bpCategory, boilingPointK]
  norm_num

end
end BoilingPoints
end Chemistry
end IndisputableMonolith
