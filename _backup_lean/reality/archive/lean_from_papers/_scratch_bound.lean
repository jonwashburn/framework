import Mathlib
import IndisputableMonolith.Constants.GapWeight.Formula
import IndisputableMonolith.Numerics.Interval.PhiBounds

open IndisputableMonolith
open IndisputableMonolith.Constants
open IndisputableMonolith.Constants.GapWeight
open IndisputableMonolith.Numerics

-- just check we can state simple inequality
#check Numerics.phi_pow8_gt
#check Constants.phi_lt_onePointSixTwo

example : (0.618 : ℝ) < (Constants.phi)⁻¹ := by
  -- use phi = goldenRatio
  have h : (0.618 : ℝ) < Real.goldenRatio⁻¹ := Numerics.phi_inv_gt
  -- rewrite
  simpa [Constants.phi] using h

