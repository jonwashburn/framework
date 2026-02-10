import IndisputableMonolith.Flight.Geometry
import IndisputableMonolith.Flight.Medium
import IndisputableMonolith.Flight.Pressure
import IndisputableMonolith.Flight.Schedule
import IndisputableMonolith.Flight.Thrust
import IndisputableMonolith.Flight.Falsifiers
import IndisputableMonolith.Flight.Report
import IndisputableMonolith.Flight.GravityBridge

/-!
# IndisputableMonolith.Flight

Spiral-Field Propulsion formalization scaffold (φ-Vortex Drive).

This module is a convenience facade that re-exports the Flight submodules.
The intent is to:
- keep mathematical lemmas provable in Lean,
- isolate physical hypotheses as explicit assumptions,
- provide executable falsifiers for lab traces.

All geometry is derived from RS constants (φ-tetrahedral angle, φ-spiral paths).

## Submodules

- `Geometry`: φ-tetrahedral angle, log-spiral rotor paths, kappa discreteness
- `Medium`: Vorticity/helicity proxy model
- `Pressure`: Pressure-vorticity coupling
- `Schedule`: 8-tick pulsed control, neutrality invariants
- `Thrust`: Net thrust aggregation
- `Falsifiers`: VacuumTest, Banding, SignFlip, PhaseLock
- `Report`: Human-readable status summary
- `GravityBridge`: **NEW** - Connects ILG weight kernel to propulsion model

Note: `IndisputableMonolith.Flight.Stability` exists but is not re-exported here yet,
since it pulls in heavier verification subtrees that are being modernized.
-/
