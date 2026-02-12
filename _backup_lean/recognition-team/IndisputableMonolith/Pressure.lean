import Mathlib
import IndisputableMonolith.Flight.Medium
import IndisputableMonolith.ILG.PressureForm

/-!
# Flight Pressure Layer

This file defines a *pressure proxy* and an explicit hypothesis interface
connecting vorticity to pressure drop.

This is where we intentionally separate:
- a **mathematical** proxy definition (always available), from
- a **physical hypothesis** that the proxy matches measured/operational pressure.
-/

namespace IndisputableMonolith
namespace Flight
namespace Pressure

open scoped Real

open IndisputableMonolith.Flight.Medium

/-- Convert the log-vorticity proxy into a positive magnitude proxy.

If `logVorticity ≈ log |ω|`, then `omegaMag ≈ |ω|`.
-/
noncomputable def omegaMag (S : MediumState) : ℝ :=
  Real.exp (absLogVorticity S)

/-- Parameters for a Bernoulli-like pressure drop proxy.

`p0` is a baseline (ambient) pressure in the chosen display units.
`cω` is a coupling coefficient (nonnegative).
-/
structure PressureParams where
  p0  : ℝ
  cω  : ℝ
  hcω : 0 ≤ cω

/-- Pressure proxy (display model): `p = p0 - cω · |ω|^2`.

This is *not* asserted to equal physical pressure until we supply a
`PressureDropFromVorticity` instance.
-/
noncomputable def pressureProxy (P : PressureParams) (S : MediumState) : ℝ :=
  P.p0 - P.cω * (omegaMag S) ^ 2

/-- Hypothesis interface: the operational pressure equals the proxy.

This should eventually be replaced by a stronger bridge theorem under a
chosen fluid model.
-/
class PressureDropFromVorticity (P : PressureParams) where
  pressure : MediumState → ℝ
  pressure_eq : ∀ S, pressure S = pressureProxy P S

/-- Convenience lemma: once the hypothesis holds, we can rewrite pressure to the proxy. -/
lemma pressure_eq_proxy (P : PressureParams) [H : PressureDropFromVorticity P] (S : MediumState) :
    H.pressure S = pressureProxy P S :=
  H.pressure_eq S

end Pressure
end Flight
end IndisputableMonolith

