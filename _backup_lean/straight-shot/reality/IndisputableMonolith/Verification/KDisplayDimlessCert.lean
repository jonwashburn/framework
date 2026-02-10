import Mathlib
import IndisputableMonolith.Verification.BridgeCore
import IndisputableMonolith.Constants.KDisplayCore

/-!
# K-Display Dimensionless Certificate

This audit certificate records that the **K-display ratios** are invariant under
anchor rescalings (`Verification.UnitsRescaled`), i.e. they are dimensionless in
the certified sense.

Concretely, it certifies that both functions

- `U ↦ (tau_rec_display U) / U.tau0`
- `U ↦ (lambda_kin_display U) / U.ell0`

are invariant under simultaneous rescaling of `(tau0, ell0)` with `c` fixed.

This is a “non-circularity / rigor” guard: it makes the scale-invariance of the
published K-gate ratios explicit in the certified surface.
-/

namespace IndisputableMonolith
namespace Verification
namespace KDisplayDimless

open IndisputableMonolith.Constants

structure KDisplayDimlessCert where
  deriving Repr

private theorem tau_ratio_dimless :
    Dimensionless (fun U : Constants.RSUnits =>
      (Constants.RSUnits.tau_rec_display U) / U.tau0) := by
  intro U U' hUU'
  by_cases hτ0 : U.tau0 = 0
  · have hτ0' : U'.tau0 = 0 := by simpa [hτ0] using hUU'.tau0
    simp [Constants.RSUnits.tau_rec_display, hτ0, hτ0']
  · have hs0 : (hUU'.s : ℝ) ≠ 0 := ne_of_gt hUU'.hs
    have hτ0' : U'.tau0 ≠ 0 := by
      have : (hUU'.s : ℝ) * U.tau0 ≠ 0 := mul_ne_zero hs0 hτ0
      simpa [hUU'.tau0] using this
    have hL : (Constants.RSUnits.tau_rec_display U) / U.tau0 = Constants.K := by
      simpa using (Constants.RSUnits.tau_rec_display_ratio U hτ0)
    have hR : (Constants.RSUnits.tau_rec_display U') / U'.tau0 = Constants.K := by
      simpa using (Constants.RSUnits.tau_rec_display_ratio U' hτ0')
    exact hL.trans hR.symm

private theorem lambda_ratio_dimless :
    Dimensionless (fun U : Constants.RSUnits =>
      (Constants.RSUnits.lambda_kin_display U) / U.ell0) := by
  intro U U' hUU'
  by_cases hℓ0 : U.ell0 = 0
  · have hℓ0' : U'.ell0 = 0 := by simpa [hℓ0] using hUU'.ell0
    simp [Constants.RSUnits.lambda_kin_display, hℓ0, hℓ0']
  · have hs0 : (hUU'.s : ℝ) ≠ 0 := ne_of_gt hUU'.hs
    have hℓ0' : U'.ell0 ≠ 0 := by
      have : (hUU'.s : ℝ) * U.ell0 ≠ 0 := mul_ne_zero hs0 hℓ0
      simpa [hUU'.ell0] using this
    have hL : (Constants.RSUnits.lambda_kin_display U) / U.ell0 = Constants.K := by
      simpa using (Constants.RSUnits.lambda_kin_display_ratio U hℓ0)
    have hR : (Constants.RSUnits.lambda_kin_display U') / U'.ell0 = Constants.K := by
      simpa using (Constants.RSUnits.lambda_kin_display_ratio U' hℓ0')
    exact hL.trans hR.symm

@[simp] def KDisplayDimlessCert.verified (_c : KDisplayDimlessCert) : Prop :=
  Dimensionless (fun U : Constants.RSUnits =>
    (Constants.RSUnits.tau_rec_display U) / U.tau0)
  ∧
  Dimensionless (fun U : Constants.RSUnits =>
    (Constants.RSUnits.lambda_kin_display U) / U.ell0)

@[simp] theorem KDisplayDimlessCert.verified_any (c : KDisplayDimlessCert) :
    KDisplayDimlessCert.verified c := by
  refine And.intro ?_ ?_
  · exact tau_ratio_dimless
  · exact lambda_ratio_dimless

end KDisplayDimless
end Verification
end IndisputableMonolith

