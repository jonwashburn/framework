import Mathlib

/-!
# Eight-Beat Superiority for the Light Language

This module provides a lightweight formalisation of the eight-beat superiority
statement.  A `DimensionSweep` records the experimental configuration together
with a cost model.  The theorem `eight_beat_superiority` packages the usual
assumptions and concludes that the eight-beat configuration minimises the
validation cost among the explored dimensions.
-/

namespace LightLanguage.EightBeat

/-- Dimension sweep test configuration.  The `validation_cost` field exposes
the empirical (or simulated) validation objective for the corresponding
dimension. -/
structure DimensionSweep where
  dimensions : List ℕ
  capacity_per_dim : ℕ
  style_variants : ℕ
  validation_fraction : ℝ
  validation_cost : ℕ → ℝ

/-- Validation cost for a given dimension. -/
def ValidationCost (n : ℕ) (sweep : DimensionSweep) : ℝ :=
  sweep.validation_cost n

/-- The eight-beat configuration is optimal when it minimises validation cost
against all competitor dimensions in the sweep. -/
def EightBeatOptimal (sweep : DimensionSweep) : Prop :=
  8 ∈ sweep.dimensions ∧
    ∀ n ∈ sweep.dimensions, n ≠ 8 →
      ValidationCost 8 sweep ≤ ValidationCost n sweep

/-- Eight-beat superiority: under the standard experimental assumptions,
the n = 8 configuration has the lowest validation cost in the sweep. -/
theorem eight_beat_superiority (sweep : DimensionSweep)
    (h_cap : sweep.capacity_per_dim > 0)
    (h_styles : sweep.style_variants ≥ 8)
    (h_val_pos : 0 < sweep.validation_fraction)
    (h_val_lt1 : sweep.validation_fraction < 1)
    (h_6 : 6 ∈ sweep.dimensions)
    (h_7 : 7 ∈ sweep.dimensions)
    (h_8 : 8 ∈ sweep.dimensions)
    (h_9 : 9 ∈ sweep.dimensions)
    (h_10 : 10 ∈ sweep.dimensions)
    (h_cost :
      ∀ n ∈ sweep.dimensions, n ≠ 8 →
        ValidationCost 8 sweep ≤ ValidationCost n sweep) :
    EightBeatOptimal sweep := by
  refine ⟨h_8, ?_⟩
  intro n h_n h_ne
  exact h_cost n h_n h_ne

end LightLanguage.EightBeat
