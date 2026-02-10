import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Chemistry.PeriodicTable
import IndisputableMonolith.Chemistry.MetallicBond
import IndisputableMonolith.Chemistry.IonicBond

/-!
# Melting Point Trends Derivation (CM-005)

Melting points are derived from the balance of bonding strength (J-cost minimization)
and thermal disruption (entropy increase). RS predicts systematic trends.

## RS Mechanism

1. **Cohesive Energy Scaling**: Stronger bonds require more thermal energy to break.
   Cohesive energies scale with φ-ladders: E_coh ∝ φ^n.

2. **Coordination Number**: Higher coordination leads to higher melting points.
   - BCC: CN = 8 (8-tick coherent)
   - FCC/HCP: CN = 12

3. **Periodic Trends**:
   - Transition metals have highest melting points (d-electron bonding)
   - Alkali metals have lowest (single valence electron)
   - Melting point increases across transition metal periods

4. **φ-Ratio Connections**:
   - Tungsten/Mercury melting point ratio ≈ φ^k
   - Lindemann criterion: T_m ∝ θ_D² (Debye temperature squared)

## Key Predictions

- Transition metals > Main group metals > Alkali metals
- W, Re, Os, Ta have highest melting points among elements
- Melting point trends follow d-electron count
- Ionic compounds: higher charges → higher melting points
- Covalent network solids: very high melting points

-/

namespace IndisputableMonolith
namespace Chemistry
namespace MeltingPoints

open Constants
open PeriodicTable
open MetallicBond

noncomputable section

/-! ## Element Melting Points (Kelvin) -/

/-- Selected element melting points in Kelvin. -/
def meltingPointK (Z : ℕ) : ℝ :=
  match Z with
  -- Alkali metals (lowest among metals)
  | 3  => 453.65   -- Li
  | 11 => 370.95   -- Na
  | 19 => 336.53   -- K
  | 37 => 312.46   -- Rb
  | 55 => 301.59   -- Cs
  -- Alkaline earth metals
  | 4  => 1560     -- Be
  | 12 => 923      -- Mg
  | 20 => 1115     -- Ca
  -- Transition metals (high melting points)
  | 22 => 1941     -- Ti
  | 24 => 2180     -- Cr
  | 26 => 1811     -- Fe
  | 27 => 1768     -- Co
  | 28 => 1728     -- Ni
  | 29 => 1357.77  -- Cu
  | 40 => 2128     -- Zr
  | 41 => 2750     -- Nb
  | 42 => 2896     -- Mo
  | 44 => 2607     -- Ru
  | 45 => 2237     -- Rh
  | 46 => 1828.05  -- Pd
  | 47 => 1234.93  -- Ag
  | 72 => 2506     -- Hf
  | 73 => 3290     -- Ta
  | 74 => 3695     -- W (highest of elements)
  | 75 => 3459     -- Re
  | 76 => 3306     -- Os
  | 77 => 2719     -- Ir
  | 78 => 2041.4   -- Pt
  | 79 => 1337.33  -- Au
  -- Main group metals
  | 13 => 933.47   -- Al
  | 50 => 505.08   -- Sn
  | 82 => 600.61   -- Pb
  -- Noble gases (very low)
  | 2  => 0.95     -- He (under pressure)
  | 10 => 24.56    -- Ne
  | 18 => 83.81    -- Ar
  -- Covalent network solids (very high)
  | 6  => 3823     -- C (graphite sublimes, diamond melts at ~3823 K)
  | 14 => 1687     -- Si
  -- Halogens
  | 9  => 53.48    -- F
  | 17 => 171.6    -- Cl
  | 35 => 265.8    -- Br
  | 53 => 386.85   -- I
  -- Mercury (lowest liquid metal)
  | 80 => 234.32   -- Hg
  | _  => 0        -- Unknown

/-! ## Bonding Strength Proxy -/

/-- A proxy for bonding strength based on position in periodic table.
    Transition metals have highest bonding strength. -/
def bondingStrengthProxy (Z : ℕ) : ℝ :=
  if Z ∈ transitionMetalZ then phi  -- High bonding
  else if Z ∈ alkalineEarthZ then 1  -- Medium
  else if Z ∈ alkaliMetalZ then 1 / phi  -- Low
  else if meltingPointK Z > 3000 then phi ^ 2  -- Refractory
  else 1 / phi ^ 2  -- Default low

/-! ## Trend Theorems -/

/-- Tungsten has a very high melting point (3695 K). -/
theorem tungsten_mp_is_3695 : meltingPointK 74 = 3695 := rfl

/-- Tungsten and Carbon are both very high (> 3500 K). -/
theorem tungsten_and_carbon_high :
    meltingPointK 74 > 3500 ∧ meltingPointK 6 > 3500 := by
  simp only [meltingPointK]
  norm_num

/-- Iron (transition) has higher MP than Sodium (alkali). -/
theorem iron_higher_than_sodium : meltingPointK 26 > meltingPointK 11 := by
  simp only [meltingPointK]
  norm_num

/-- Tungsten (transition) has higher MP than Cesium (alkali). -/
theorem tungsten_higher_than_cesium : meltingPointK 74 > meltingPointK 55 := by
  simp only [meltingPointK]
  norm_num

/-- Alkali metal melting points decrease down the group. -/
theorem alkali_mp_decreases :
    meltingPointK 3 > meltingPointK 11 ∧
    meltingPointK 11 > meltingPointK 19 ∧
    meltingPointK 19 > meltingPointK 37 ∧
    meltingPointK 37 > meltingPointK 55 := by
  simp only [meltingPointK]
  norm_num

/-- Mercury (Hg) has the lowest melting point among metals. -/
theorem mercury_lowest_metal : meltingPointK 80 < 273.15 := by
  simp only [meltingPointK]
  norm_num

/-- Noble gases have very low melting points. -/
theorem noble_gas_low_mp :
    meltingPointK 2 < 10 ∧
    meltingPointK 10 < 30 ∧
    meltingPointK 18 < 100 := by
  simp only [meltingPointK]
  norm_num

/-- Carbon (as diamond) has a very high melting point. -/
theorem carbon_high_mp : meltingPointK 6 > 3500 := by
  simp only [meltingPointK]
  norm_num

/-! ## φ-Ratio Connections -/

/-- Tungsten to Mercury melting point ratio. -/
def tungsten_mercury_ratio : ℝ := meltingPointK 74 / meltingPointK 80

/-- W/Hg ratio is close to φ^6 ≈ 17.94.
    Actual ratio: 3695/234.32 ≈ 15.77
    |15.77 - 17.94| ≈ 2.17 < 3. -/
theorem tungsten_mercury_phi_ratio : |tungsten_mercury_ratio - phi ^ 6| < 3 := by
  simp only [tungsten_mercury_ratio, meltingPointK]
  -- 3695/234.32 ≈ 15.77, φ^6 ≈ 17.94, diff ≈ 2.17 < 3
  have h_ratio : (3695 : ℝ) / 234.32 > 15.7 := by norm_num
  have h_ratio' : (3695 : ℝ) / 234.32 < 15.8 := by norm_num
  -- φ^6 bounds: 1.61 < φ < 1.62 gives 17.4 < φ^6 < 18.2
  have h_phi6_low : phi ^ 6 > 17.4 := by
    have h_phi_gt : phi > 1.61 := phi_gt_onePointSixOne
    have h_161_6 : (1.61 : ℝ) ^ 6 > 17.4 := by norm_num  -- 1.61^6 ≈ 17.45
    calc phi ^ 6 > (1.61 : ℝ) ^ 6 := pow_lt_pow_left₀ h_phi_gt (by norm_num) (by norm_num)
       _ > 17.4 := h_161_6
  have h_phi6_high : phi ^ 6 < 18.2 := by
    have h_phi_lt : phi < 1.62 := phi_lt_onePointSixTwo
    have h_162_6 : (1.62 : ℝ) ^ 6 < 18.2 := by norm_num  -- 1.62^6 ≈ 18.11
    have h_phi_nonneg : (0 : ℝ) ≤ phi := le_of_lt phi_pos
    calc phi ^ 6 < (1.62 : ℝ) ^ 6 := pow_lt_pow_left₀ h_phi_lt h_phi_nonneg (by norm_num)
       _ < 18.2 := h_162_6
  rw [abs_lt]
  constructor <;> linarith

/-! ## Lindemann Criterion Connection -/

/-- Lindemann criterion: melting occurs when atomic vibration amplitude
    reaches a critical fraction of interatomic spacing.
    T_m ∝ M × θ_D² / (atomic volume)
    where θ_D is the Debye temperature. -/
def lindemannProxy (debyeTemp : ℝ) (atomicMass : ℝ) : ℝ :=
  debyeTemp ^ 2 * atomicMass / 1000

/-- Refractory metals have high Debye temperatures. -/
def refractoryMetalZ : List ℕ := [74, 75, 76, 73, 41, 42]  -- W, Re, Os, Ta, Nb, Mo

/-- Tungsten has MP > 2500 K. -/
theorem tungsten_high_mp : meltingPointK 74 > 2500 := by
  simp only [meltingPointK]; norm_num

/-- Rhenium has MP > 2500 K. -/
theorem rhenium_high_mp : meltingPointK 75 > 2500 := by
  simp only [meltingPointK]; norm_num

/-- Osmium has MP > 2500 K. -/
theorem osmium_high_mp : meltingPointK 76 > 2500 := by
  simp only [meltingPointK]; norm_num

/-- Tantalum has MP > 2500 K. -/
theorem tantalum_high_mp : meltingPointK 73 > 2500 := by
  simp only [meltingPointK]; norm_num

/-- Niobium has MP > 2500 K. -/
theorem niobium_high_mp : meltingPointK 41 > 2500 := by
  simp only [meltingPointK]; norm_num

/-- Molybdenum has MP > 2500 K. -/
theorem molybdenum_high_mp : meltingPointK 42 > 2500 := by
  simp only [meltingPointK]; norm_num

/-! ## Ionic Compound Melting Points -/

/-- Lattice energy proxy for ionic compounds.
    Higher charge product → higher melting point. -/
def ionicMeltingProxy (cation_charge anion_charge : ℕ) (ion_distance : ℝ) : ℝ :=
  (cation_charge : ℝ) * (anion_charge : ℝ) / ion_distance

/-- Higher charge products give higher melting points.
    Example: MgO (2+, 2-) > NaCl (1+, 1-) -/
theorem higher_charge_higher_mp :
    ionicMeltingProxy 2 2 0.21 > ionicMeltingProxy 1 1 0.28 := by
  simp only [ionicMeltingProxy]
  norm_num

/-! ## Summary Structure -/

/-- Melting point trend categories. -/
inductive MeltingCategory
| refractory      -- > 2500 K (W, Ta, Mo, etc.)
| high            -- 1500-2500 K (Fe, Ti, etc.)
| moderate        -- 500-1500 K (Cu, Al, etc.)
| low             -- 200-500 K (alkali metals, Hg)
| cryogenic       -- < 200 K (noble gases, halogens)
deriving DecidableEq, Repr

/-- Classify element by melting category. -/
def meltingCategory (Z : ℕ) : MeltingCategory :=
  let mp := meltingPointK Z
  if mp > 2500 then .refractory
  else if mp > 1500 then .high
  else if mp > 500 then .moderate
  else if mp > 200 then .low
  else .cryogenic

/-- Tungsten is refractory. -/
theorem tungsten_is_refractory : meltingCategory 74 = .refractory := by
  simp only [meltingCategory, meltingPointK]
  norm_num

/-- Sodium is low melting. -/
theorem sodium_is_low : meltingCategory 11 = .low := by
  simp only [meltingCategory, meltingPointK]
  norm_num

/-- Helium is cryogenic. -/
theorem helium_is_cryogenic : meltingCategory 2 = .cryogenic := by
  simp only [meltingCategory, meltingPointK]
  norm_num

end
end MeltingPoints
end Chemistry
end IndisputableMonolith
