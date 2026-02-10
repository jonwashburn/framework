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

Note: `IndisputableMonolith.Flight.Stability` exists but is not re-exported here yet,
since it pulls in heavier verification subtrees that are being modernized.
-/
