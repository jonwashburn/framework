import Mathlib
import IndisputableMonolith.Flight.Geometry
import IndisputableMonolith.Flight.Schedule
import IndisputableMonolith.Flight.Falsifiers

/-!
# Flight Report

Small, human-readable report helpers for the Flight subtheory.

The goal is to mirror other “report” style modules in the repo: expose
lightweight indicators of what is proved vs. assumed, and what falsifiers
exist.
-/

namespace IndisputableMonolith
namespace Flight

/-- A tiny, display-level status summary for the Flight subtheory.

This is intentionally a pure string (not JSON) so it can be printed from Lean.

All terminology is RS-native (no third-party branding).
-/
def FlightReport : String :=
  String.intercalate "\n" [
    "FlightReport (IndisputableMonolith.Flight) — Spiral-Field Propulsion",
    "",
    "[M] Theorems proved (φ-geometry + 8-gate):",
    "- Flight.Geometry.SpiralLemmas.logSpiral_ne_zero",
    "- Flight.Geometry.SpiralLemmas.stepRatio_logSpiral_closed_form",
    "- Flight.Geometry.SpiralLemmas.stepRatio_invariant_under_r0",
    "- Flight.Geometry.SpiralLemmas.perTurn_ratio",
    "- Flight.Geometry.SpiralLemmas.kappa_discreteness",
    "- Flight.Schedule.eightGateNeutral_shift_invariance (under Schedule.Periodic8)",
    "",
    "Key RS definitions:",
    "- Flight.Geometry.phiTetrahedralAngle (arccos(-1/3) ≈ 109.47°)",
    "- Flight.Geometry.RotorPitch (φ-spiral pitch family)",
    "- Flight.Schedule.DriveSchedule (8-tick window discipline)",
    "",
    "Falsifiers implemented:",
    "- Flight.Falsifiers.VacuumTestFalsifier",
    "- Flight.Falsifiers.BandingFalsifier",
    "- Flight.Falsifiers.SignFlipFalsifier",
    "- Flight.Falsifiers.PhaseLockFalsifier",
    "",
    "Notes:",
    "- Medium model is currently a local proxy (decoupled from LNAL VM) for build stability.",
    "- Stability/NS bridge is planned as an optional module, not re-exported by Flight.lean yet."
  ]

end Flight
end IndisputableMonolith
