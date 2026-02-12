import Mathlib

/-!
Helpers for 4D lattice indexing and plaquette boundary enumeration.

Cycle-free: this module only speaks in raw coordinate data and directions
(`Fin 4` indices). It intentionally does not depend on `YMFramework` types.
-/

namespace YM
namespace Lattice
namespace Geometry

open Classical

abbrev Point4 := Fin 4 × Fin 4 × Fin 4 × Fin 4

/-- Increment one of the four coordinates (periodic mod 4) in the + direction. -/
def stepPlus (x : Point4) (dir : Fin 4) : Point4 :=
  let (x0, x1, x2, x3) := x
  have inc : Fin 4 → Fin 4 := fun y => Fin.ofNat (y.val + 1)
  match dir with
  | ⟨0, _⟩ => (inc x0, x1, x2, x3)
  | ⟨1, _⟩ => (x0, inc x1, x2, x3)
  | ⟨2, _⟩ => (x0, x1, inc x2, x3)
  | ⟨3, _⟩ => (x0, x1, x2, inc x3)

/-- Decrement one of the four coordinates (periodic mod 4) in the − direction. -/
def stepMinus (x : Point4) (dir : Fin 4) : Point4 :=
  let (x0, x1, x2, x3) := x
  -- `y - 1 (mod 4)` is `y + 3 (mod 4)`
  have dec : Fin 4 → Fin 4 := fun y => Fin.ofNat (y.val + 3)
  match dir with
  | ⟨0, _⟩ => (dec x0, x1, x2, x3)
  | ⟨1, _⟩ => (x0, dec x1, x2, x3)
  | ⟨2, _⟩ => (x0, x1, dec x2, x3)
  | ⟨3, _⟩ => (x0, x1, x2, dec x3)

/-- The four positively-oriented link data around the plaquette with given
corner `x` and plane `(μ, ν)`. The links are listed in fixed order:
0: along `μ` from `x`; 1: along `ν` from `x+μ`; 2: along `μ` from `x+ν`;
3: along `ν` from `x`.

In a Wilson plaquette product, links 0 and 1 are used as-is, and links 2 and 3
are taken with inverse to traverse the boundary in the standard orientation.
-/
def plaquetteLinks (corner : Point4) (plane : Fin 4 × Fin 4) : Fin 4 → (Point4 × Fin 4)
  | ⟨0, _⟩ => (corner, plane.1)
  | ⟨1, _⟩ => (stepPlus corner plane.1, plane.2)
  | ⟨2, _⟩ => (stepPlus corner plane.2, plane.1)
  | ⟨3, _⟩ => (corner, plane.2)

end Geometry
end Lattice
end YM


