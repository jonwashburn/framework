import Mathlib
import IndisputableMonolith.RH.RS.Spec

/-!
# UniqueCalibration Certificate (absolute-layer calibration is explicit)

This certificate packages the lemma `IndisputableMonolith.RH.RS.uniqueCalibration_any`:
for every ledger/bridge and every anchor pair, there is a *unique* RS-units pack
calibrated to those anchors (with the speed determined by `speedFromAnchors`).

This is an **audit** certificate: it makes the “absolute-layer calibration witness”
explicit and machine-checked, rather than relying on implicit choice.
-/

namespace IndisputableMonolith
namespace Verification
namespace UniqueCalibration

open IndisputableMonolith.RH

structure UniqueCalibrationCert where
  deriving Repr

@[simp] def UniqueCalibrationCert.verified (_c : UniqueCalibrationCert) : Prop :=
  ∀ (L : RH.RS.Ledger) (B : RH.RS.Bridge L) (A : RH.RS.Anchors),
    RH.RS.UniqueCalibration L B A

@[simp] theorem UniqueCalibrationCert.verified_any (c : UniqueCalibrationCert) :
    UniqueCalibrationCert.verified c := by
  intro L B A
  exact RH.RS.uniqueCalibration_any L B A

end UniqueCalibration
end Verification
end IndisputableMonolith
