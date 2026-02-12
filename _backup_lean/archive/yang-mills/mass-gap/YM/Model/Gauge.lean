import Mathlib

/-!
Gauge model scaffold with a Real-native SU(N) plaquette trace.
No axioms. No `sorry`.
 - `plaquetteTrace4` implements Wilson's single-plaquette contribution with the
   conventional normalization `1 - (1/N) Re Tr(U_μν)`.
-/

namespace YM.Model.Gauge

open Complex

/-- Real-valued SU(N) plaquette trace with Wilson normalization.

`1 - (1/N) · Re(Tr(a b c d))`, where `a,b,c,d ∈ SU(N)` are the four oriented
link matrices around a plaquette boundary, ordered so that the last two entries
are the inverses corresponding to reversed links on the boundary.

Reference: Wilson action normalization in the manuscript (Yang-Mills-sept21.tex).
-/
def plaquetteTrace4 {N : Nat}
  (a b c d : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  1 - (1 / (N : ℝ)) * Complex.realPart
        (Matrix.trace (((a : Matrix (Fin N) (Fin N) ℂ)
                          ⬝ (b : Matrix (Fin N) (Fin N) ℂ)
                          ⬝ (c : Matrix (Fin N) (Fin N) ℂ)
                          ⬝ (d : Matrix (Fin N) (Fin N) ℂ))))

end YM.Model.Gauge


namespace YM.Model.Gauge

open Complex

/--
Real-normalized SU(N) plaquette trace helper independent of links/plaquettes.

Alias matching the requested symbol name, using the conventional Wilson
normalization implemented by `plaquetteTrace4`.
-/
def plaquetteTrace {N : Nat}
    (a b c d : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  plaquetteTrace4 (N := N) a b c d

end YM.Model.Gauge

