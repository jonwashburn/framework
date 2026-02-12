import Mathlib

/-!
# Time Calibration (RS units → years)

This module centralizes the **explicit calibration factor** needed to interpret
dimensionless/RS-time-unit quantities as **years**.

## Scientific hygiene
- This is **not derived** from the Θ-stack: it is an empirical / conventions layer.
- Downstream modules should accept a `TimeCalibration` parameter when they produce
  year-scale outputs, rather than smuggling constants.
-/

namespace IndisputableMonolith.Consciousness

/-- A positive conversion factor from RS-time-units to years.

Interpretation: if a process takes `t_RS` RS-units, then it takes
`t_years = t_RS * rs_to_years` years under this calibration. -/
structure TimeCalibration where
  rs_to_years : ℝ
  h_pos : 0 < rs_to_years

/-- Convert an RS-time quantity to years using an explicit calibration factor. -/
noncomputable def toYears (cal : TimeCalibration) (t_RS : ℝ) : ℝ :=
  t_RS * cal.rs_to_years

theorem toYears_pos (cal : TimeCalibration) {t_RS : ℝ} (ht : 0 < t_RS) :
    0 < toYears cal t_RS := by
  unfold toYears
  exact mul_pos ht cal.h_pos

end IndisputableMonolith.Consciousness
