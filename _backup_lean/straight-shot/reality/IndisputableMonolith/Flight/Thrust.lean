import Mathlib
import IndisputableMonolith.Flight.Medium
import IndisputableMonolith.Flight.Pressure

/-!
# Flight Thrust Layer

Defines a minimal “thrust observable” interface.

At this stage, we do not attempt a full continuum derivation (surface integrals,
control volumes, etc.). Instead we:
- define a vector type,
- define a placeholder thrust observable,
- provide hypothesis interfaces that can later be strengthened.
-/

namespace IndisputableMonolith
namespace Flight
namespace Thrust

open IndisputableMonolith.Flight

/-- Minimal 3-vector type for thrust/acceleration. -/
abbrev Vec3 := ℝ × ℝ × ℝ

/-- Placeholder thrust observable on a medium state.

This will be refined to a pressure-gradient / control-volume expression.
-/
noncomputable def thrustVector (_S : Medium.MediumState) : Vec3 := (0, 0, 0)

/-- Aggregate thrust over a finite tick window `[t0, t0+N)`.

At this stage we treat the thrust vector as externally provided per tick.
-/
noncomputable def netThrust (f : ℕ → Vec3) (t0 N : ℕ) : Vec3 :=
  ( (Finset.range N).sum (fun k => (f (t0 + k)).1)
  , (Finset.range N).sum (fun k => (f (t0 + k)).2.1)
  , (Finset.range N).sum (fun k => (f (t0 + k)).2.2) )

end Thrust
end Flight
end IndisputableMonolith

