import Mathlib
import IndisputableMonolith.Flight.Schedule
import IndisputableMonolith.Flight.Thrust

/-!
# Flight Falsifiers

Executable predicates over recorded traces.

These are intentionally simple “interfaces” at first: the goal is to
encode *what must be true in data* if the physical hypotheses are true.

As the physical model tightens, these falsifiers should become stricter.
-/

namespace IndisputableMonolith
namespace Flight
namespace Falsifiers

open IndisputableMonolith.Flight

/-- Minimal experimental trace schema (display-level).

This is intentionally small and can be extended.
-/
structure Trace where
  /-- Ambient pressure (e.g., vacuum chamber pressure) as a function of time tick. -/
  ambientPressure : ℕ → ℝ
  /-- Commanded schedule (pulse/no-pulse). -/
  schedule : Schedule.DriveSchedule
  /-- Measured thrust vector (or inferred acceleration proxy). -/
  thrust : ℕ → Thrust.Vec3

/-- Vacuum persistence falsifier:

If thrust remains nonzero while ambient pressure is lowered below a threshold,
then the claim is *consistent* with non-aerodynamic propulsion.

(This is a *one-way* falsifier: failure does not disprove the model unless
we control for other conditions.)
-/
def VacuumTestFalsifier (p_max : ℝ) (Tmin : ℝ) (tr : Trace) : Prop :=
  (∃ t, tr.ambientPressure t ≤ p_max ∧ (tr.thrust t).2.2 ≥ Tmin)

/-- Banding falsifier:

There exist times `t1 < t2 < t3` with similar ambient pressure but discrete
thrust states (off/on/off). This encodes the “banded operating regimes” claim.
-/
def BandingFalsifier (εp : ℝ) (Tmin : ℝ) (tr : Trace) : Prop :=
  ∃ t1 t2 t3,
    t1 < t2 ∧ t2 < t3 ∧
    |tr.ambientPressure t1 - tr.ambientPressure t2| ≤ εp ∧
    |tr.ambientPressure t2 - tr.ambientPressure t3| ≤ εp ∧
    (tr.thrust t1).2.2 < Tmin ∧
    (tr.thrust t2).2.2 ≥ Tmin ∧
    (tr.thrust t3).2.2 < Tmin

/-- Sign-flip falsifier:

Under a schedule “handedness flip” (modeled externally), thrust should flip sign.

At the trace level, we encode this as the existence of two segments with
opposite-signed vertical thrust.
-/
def SignFlipFalsifier (Tmin : ℝ) (tr : Trace) : Prop :=
  ∃ tpos tneg,
    (tr.thrust tpos).2.2 ≥ Tmin ∧
    (tr.thrust tneg).2.2 ≤ -Tmin

/-- Phase-lock falsifier (display-level):

There exist two times `t1 < t2` under sustained pulsing such that the thrust
proxy decays significantly.

This encodes the *failure mode* claim (“continuous forcing degrades performance”).
It does **not** yet encode the “pulsing restores it” part; that will require
either richer trace fields (power/temperature) or explicit segment labels.
-/
def PhaseLockFalsifier (window : ℕ) (drop : ℝ) (tr : Trace) : Prop :=
  ∃ t1 t2,
    t1 < t2 ∧
    (∀ t, t1 ≤ t ∧ t < t1 + window → (tr.schedule t).pulse = true) ∧
    (∀ t, t2 ≤ t ∧ t < t2 + window → (tr.schedule t).pulse = true) ∧
    (tr.thrust t1).2.2 - (tr.thrust t2).2.2 ≥ drop

end Falsifiers
end Flight
end IndisputableMonolith

