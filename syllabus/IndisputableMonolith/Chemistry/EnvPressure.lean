import Mathlib
import IndisputableMonolith.Constants

/-!
# Environment Display Rescale (scaffold)

Display-only rescale for environment-dependent observables: E → E · φ^{β P},
leaving integer scaffolding intact. β is a fixed constant determined by
neutrality tests; this file exposes helpers and diagnostics only.
-/

namespace IndisputableMonolith
namespace Chemistry
namespace EnvPressure

open scoped Real

/‑ Environment scale factor: φ^{β P}. -/
def scaleFactor (beta P : ℝ) : ℝ :=
  Real.rpow IndisputableMonolith.Constants.phi (beta * P)

/‑ Display rescale: E' = E · φ^{β P}. -/
def rescaleEnergy (E beta P : ℝ) : ℝ := E * scaleFactor beta P

/‑ Eight-window neutrality diagnostic on a display observable stream x. -/
def neutral8 (x : ℕ → ℝ) (t0 : ℕ) : ℝ :=
  (Finset.range 8).sum (fun i => x (t0 + i))

end EnvPressure
end Chemistry
end IndisputableMonolith
