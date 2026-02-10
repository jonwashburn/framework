import Mathlib
import IndisputableMonolith.Flight.Medium
import IndisputableMonolith.Verification.CPMBridge.Domain.NavierStokes
import IndisputableMonolith.Verification.CPMBridge.DomainCertificates.NavierStokes

/-!
# Flight Stability Layer

This file connects the Flight medium (discrete vorticity proxy) to the existing
Navier–Stokes CPM bridge scaffolding.

At this stage:
- we do not prove Navier–Stokes regularity;
- we *do* reuse the existing certificate windows (e.g., `bmo_threshold ≤ 0.2`)
  to define an operational “safe gate”.
-/

namespace IndisputableMonolith
namespace Flight
namespace Stability

open IndisputableMonolith.Flight.Medium

open IndisputableMonolith.Verification

/-- Alias: the certificate type used to parameterize small-data gates. -/
abbrev NavierStokesCertificate :=
  IndisputableMonolith.Verification.CPMBridge.DomainCertificates.NavierStokesCertificate

/-- Operational small-data gate: center voxel vorticity proxy stays under the certificate threshold. -/
def withinBMO (C : NavierStokesCertificate) (S : MediumState) : Prop :=
  absLogVorticity S ≤ C.bmo_threshold

/-- The canonical certificate from the CPM bridge is small (display-level bound). -/
lemma classical_bmo_small :
    (IndisputableMonolith.Verification.CPMBridge.DomainCertificates.NavierStokes.classical).bmo_threshold ≤ 0.2 :=
  IndisputableMonolith.Verification.CPMBridge.DomainCertificates.NavierStokes.classical_bmo_threshold_small

end Stability
end Flight
end IndisputableMonolith

