import Mathlib
import IndisputableMonolith.Numerics.Interval.PhiBounds
import IndisputableMonolith.Constants

open IndisputableMonolith
open IndisputableMonolith.Constants
open IndisputableMonolith.Numerics

example : (0.618 : ℝ) < phi⁻¹ := by
  -- from Numerics: 0.618 < goldenRatio⁻¹
  have h : (0.618 : ℝ) < Real.goldenRatio⁻¹ := Numerics.phi_inv_gt
  -- our phi is definitional equal
  simpa [Constants.phi] using h
