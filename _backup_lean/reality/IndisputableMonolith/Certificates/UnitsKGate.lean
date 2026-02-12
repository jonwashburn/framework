import Mathlib
import IndisputableMonolith.Constants.KDisplay

namespace IndisputableMonolith
namespace Certificates

open IndisputableMonolith.Constants

/-! # Units / K-gate Audit Certificate

Evaluates the K-gate identities (time-first vs length-first displays) on a
canonical RS units pack and on a rescaled pack, ensuring the quotient is
dimensionless and invariant under admissible rescalings.
-/

/-- Absolute difference helper for floats. -/
@[inline] def floatAbs (x : Float) : Float := Float.abs x

/-- Approximate equality for floats with configurable tolerance. -/
@[inline] def approxEq (a b : Float) (tol : Float := 1e-6) : Bool :=
  floatAbs (a - b) ≤ tol

/-- Compute the τ-route and λ-route ratios for a given RSUnits pack. -/
noncomputable def computeRatios (U : RSUnits) : Float × Float :=
  let clock : ℝ := RSUnits.tau_rec_display U / U.tau0
  let length : ℝ := RSUnits.lambda_kin_display U / U.ell0
  (Real.toFloat clock, Real.toFloat length)

/-- Units/K-gate certificate with diagnostic ratios. -/
structure UnitsKGateCert where
  ok               : Bool
  tolerance        : Float := 1e-6
  baseClockRatio   : Float
  baseLengthRatio  : Float
  scaledClockRatio : Float
  scaledLengthRatio : Float
  errors           : List String := []
deriving Repr

@[simp] def UnitsKGateCert.verified (c : UnitsKGateCert) : Prop := c.ok = true

noncomputable def UnitsKGateCert.fromSource (_src : String) : UnitsKGateCert :=
  let base : RSUnits := { tau0 := 1, ell0 := 1, c := 1, c_ell0_tau0 := by simp }
  let scaled : RSUnits := { tau0 := 2, ell0 := 2, c := 1, c_ell0_tau0 := by simp }
  let (baseClock, baseLength) := computeRatios base
  let (scaledClock, scaledLength) := computeRatios scaled
  let tol : Float := 1e-6
  let baseMatch := approxEq baseClock baseLength tol
  let baseMatchesK := approxEq baseClock (Float.ofInt 1) tol
  let scaledMatch := approxEq scaledClock scaledLength tol
  let crossMatch := approxEq baseClock scaledClock tol
  let ok := baseMatch && baseMatchesK && scaledMatch && crossMatch
  let errors :=
    if ok then []
    else ["Units/K-gate mismatch detected (τ-route vs λ-route)"]
  { ok := ok,
    tolerance := tol,
    baseClockRatio := baseClock,
    baseLengthRatio := baseLength,
    scaledClockRatio := scaledClock,
    scaledLengthRatio := scaledLength,
    errors := errors }

end Certificates
end IndisputableMonolith
