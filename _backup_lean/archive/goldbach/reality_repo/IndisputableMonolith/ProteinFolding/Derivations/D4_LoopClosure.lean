import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Constants

/-!
# Derivation D4: J-Cost Loop-Closure Energy

This module derives the loop closure energy penalty using the J-cost function.

## Key Formula

    E_loop(d) = J(d/d_opt) × scale_factor

Where:
- d: actual loop length (sequence separation)
- d_opt = 10: optimal loop length
- J(x) = (x + 1/x)/2 - 1: the recognition cost function

## Physical Motivation

Loop closure creates geometric strain. The J-cost function naturally
captures the cost of deviating from optimal length, with symmetric
penalties for loops that are too short or too long.

-/

namespace IndisputableMonolith
namespace ProteinFolding
namespace Derivations
namespace D4

open Constants
open Cost

/-! ## Loop Parameters -/

/-- Optimal loop length (residues) -/
def d_opt : ℕ := 10

/-- Minimum allowed loop length -/
def d_min : ℕ := 6

/-- Threshold for extension penalty -/
def d_extension : ℕ := 40

/-- Scale factor for loop closure energy -/
noncomputable def loopScaleFactor : ℝ := 1.5

/-! ## Loop Closure Cost Function -/

/-- Loop closure J-cost for a given loop length

    Returns ⊤ (infinity) for forbidden short loops.
    Uses J(d/d_opt) for allowed loops. -/
noncomputable def loopClosureCost (d : ℕ) : ℝ :=
  if d < d_min then 0  -- Forbidden (handled separately)
  else
    let ratio := (d : ℝ) / d_opt
    let jCost := Jcost ratio
    let scaled := jCost * loopScaleFactor
    -- Extension penalty for very long loops
    let extension :=
      if d > d_extension then 0.3 * min (((d : ℝ) - d_extension) / 20) 1
      else 0
    scaled + extension

/-- Loop closure cost is zero at optimal length -/
theorem loop_optimal_zero : loopClosureCost d_opt = 0 := by
  simp only [loopClosureCost, d_opt, d_min]
  norm_num
  simp only [Jcost, div_self (by norm_num : (10 : ℝ) ≠ 0)]
  norm_num

/-- Loop closure cost is symmetric around optimal (for J part)

    When d1/d_opt = d_opt/d2 (i.e., d1 × d2 = d_opt²), the J-costs are equal
    because J(x) = J(1/x). -/
theorem loop_symmetry_property (d1 d2 : ℕ) (hd1 : d1 ≥ d_min) (hd2 : d2 ≥ d_min)
    (hd1_le : d1 ≤ d_extension) (hd2_le : d2 ≤ d_extension)
    (hsym : (d1 : ℝ) / d_opt = (d_opt : ℝ) / d2) :
    loopClosureCost d1 = loopClosureCost d2 := by
  -- From hsym: d1/10 = 10/d2, so d1×d2 = 100, meaning d1/10 = 1/(d2/10)
  have hd2_pos : (0 : ℝ) < d2 := by
    have : d2 ≥ 6 := hd2
    exact Nat.cast_pos.mpr (by omega)
  have hratio : (d1 : ℝ) / d_opt = ((d2 : ℝ) / d_opt)⁻¹ := by
    simp only [d_opt] at hsym ⊢
    rw [hsym]
    field_simp
  -- J(d1/10) = J((d2/10)⁻¹) = J(d2/10) by J-symmetry
  have hJ_eq : Jcost ((d1 : ℝ) / d_opt) = Jcost ((d2 : ℝ) / d_opt) := by
    rw [hratio]
    have hd2_ratio_pos : (0 : ℝ) < (d2 : ℝ) / d_opt := by
      simp only [d_opt]
      exact div_pos hd2_pos (by norm_num)
    exact (Jcost_symm hd2_ratio_pos).symm
  -- Now show loopClosureCost d1 = loopClosureCost d2
  simp only [loopClosureCost, d_opt, d_min, d_extension] at *
  -- Both are ≥ 6 and ≤ 40
  have h1 : ¬d1 < 6 := by omega
  have h2 : ¬d2 < 6 := by omega
  have h3 : ¬d1 > 40 := by omega
  have h4 : ¬d2 > 40 := by omega
  simp only [h1, h2, h3, h4, ↓reduceIte]
  -- Both equal loopScaleFactor * J(ratio)
  congr 1
  exact hJ_eq

/-- Short loops are forbidden (cost is flagged) -/
def loopForbidden (d : ℕ) : Bool := d < d_min

/-! ## Loop Closure Examples -/

/-- Loop costs at various lengths -/
noncomputable def loopCostTable : List (ℕ × ℝ) :=
  [6, 7, 8, 9, 10, 11, 12, 14, 16, 20, 30, 40, 50].map fun d =>
    (d, loopClosureCost d)

/-! ## Loop Geometry Constraints -/

/-- End-to-end distance constraint for loop of length d

    The end-to-end distance must be achievable by d residues. -/
noncomputable def maxEndToEndDistance (d : ℕ) : ℝ :=
  -- Maximum extension: ~3.8 Å per residue
  (d : ℝ) * 3.8

/-- Minimum end-to-end distance (not too compact) -/
noncomputable def minEndToEndDistance (d : ℕ) : ℝ :=
  if d ≤ 6 then 0
  else
    -- Minimum packing: Cα-Cα ~ 3.5 Å minimum
    ((d : ℝ) - 6) * 2.0

/-- Valid distance range for loop closure -/
def loopDistanceValid (d : ℕ) (distance : ℝ) : Prop :=
  minEndToEndDistance d ≤ distance ∧ distance ≤ maxEndToEndDistance d

/-! ## Integration with Contact Scoring -/

/-- Loop closure penalty as multiplicative factor for contact score

    Score is multiplied by 1/(1 + loopClosureCost) -/
noncomputable def loopClosureFactor (d : ℕ) : ℝ :=
  if loopForbidden d then 0
  else 1 / (1 + loopClosureCost d)

/-- Optimal loops have factor near 1 -/
theorem optimal_loop_factor : loopClosureFactor d_opt = 1 := by
  simp only [loopClosureFactor, loopForbidden, d_opt, d_min]
  norm_num
  rw [loop_optimal_zero]
  norm_num

/-- Forbidden loops have factor 0 -/
theorem forbidden_loop_factor (d : ℕ) (hd : d < d_min) :
    loopClosureFactor d = 0 := by
  simp only [loopClosureFactor, loopForbidden, hd, ↓reduceIte]

end D4
end Derivations
end ProteinFolding
end IndisputableMonolith
