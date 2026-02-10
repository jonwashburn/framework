import Mathlib
import IndisputableMonolith.Consciousness.LightField

/-!
# Light Field Density (Scaffold)

Defines a minimal notion of region-average “pattern density” for Light Memory patterns
located in the (currently 1D) Light Field.

This is intentionally conservative:
- we use **finite** sets (`Finset`) of located patterns,
- and a simple interval region with positive volume.

No claims about the physical meaning of “density” are made here; this is scaffolding
needed to *state* saturation/capacity questions.
-/

namespace IndisputableMonolith
namespace Consciousness

open IntervalRegion

/-! ## Counts and densities in an interval region -/

/-- Count how many located patterns have positions inside the interval region. -/
noncomputable def countInInterval
    (patterns : Finset LocatedLightMemory)
    (R : IntervalRegion) : ℕ := by
  classical
  exact (patterns.filter (fun p => decide (R.Contains p.pos))).card

/-- Region-average density: count divided by region volume. -/
noncomputable def densityInInterval
    (patterns : Finset LocatedLightMemory)
    (R : IntervalRegion) : ℝ :=
  (countInInterval patterns R : ℝ) / R.volume

/-- Density is nonnegative. -/
theorem densityInInterval_nonneg
    (patterns : Finset LocatedLightMemory)
    (R : IntervalRegion) :
    0 ≤ densityInInterval patterns R := by
  unfold densityInInterval
  have hv : 0 < R.volume := R.volume_pos
  have hcv : 0 ≤ (countInInterval patterns R : ℝ) := by
    exact Nat.cast_nonneg _
  exact div_nonneg hcv (le_of_lt hv)

/-! ## Useful helper: density from a raw count -/

/-- Density computed from a raw count (useful for monotonicity lemmas). -/
noncomputable def densityFromCount (count : ℕ) (R : IntervalRegion) : ℝ :=
  (count : ℝ) / R.volume

theorem densityFromCount_nonneg (count : ℕ) (R : IntervalRegion) :
    0 ≤ densityFromCount count R := by
  unfold densityFromCount
  have hv : 0 < R.volume := R.volume_pos
  exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hv)

theorem densityFromCount_mono {c₁ c₂ : ℕ} (hc : c₁ ≤ c₂) (R : IntervalRegion) :
    densityFromCount c₁ R ≤ densityFromCount c₂ R := by
  unfold densityFromCount
  have hv : 0 < R.volume := R.volume_pos
  -- Divide by a nonnegative real preserves order.
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hc) (le_of_lt hv)

end Consciousness
end IndisputableMonolith


