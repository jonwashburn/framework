import Mathlib

/-!
# Flight Medium (Aether / Light Field) — discrete scaffold

This file defines a minimal “medium state” interface usable by Flight proofs.

At this stage we do **not** claim a continuum Navier–Stokes model; we simply
use a discrete vorticity proxy.

Note: this is intentionally **decoupled** from `IndisputableMonolith.LNAL` for
now because the LNAL invariants subtheory is being actively modernized to the
current toolchain/mathlib.
-/

namespace IndisputableMonolith
namespace Flight
namespace Medium

open scoped Real

/-! ## Discrete vorticity proxy -/

/-- Local vorticity voxel proxy for Flight.

This mirrors the shape of the LNAL `VorticityVoxel` record, but lives in the
Flight namespace so Flight can compile independently of the larger VM stack.
-/
structure VorticityVoxel where
  /-- Signed log-vorticity proxy (display units). -/
  logVorticity    : ℝ
  /-- Stream function proxy (display units). -/
  streamFunction  : ℝ := 0
  /-- Parity/sign channel (integer lattice). -/
  signParity      : Int := 1
  /-- Coarse time slice / tick index. -/
  timeSlice       : Nat := 0
  /-- Discrete velocity mode. -/
  velocityMode    : Int := 0
  /-- Discrete phase index. -/
  vorticityPhase  : Int := 0

/-- A minimal medium state: a center voxel plus a neighborhood.

This intentionally mirrors the way the LNAL VM would evolve a local patch.
-/
structure MediumState where
  center    : VorticityVoxel
  neighbors : List VorticityVoxel

/-- Convenience: the signed log-vorticity at the center voxel.

`logVorticity` is treated as a φ-quantized proxy for `log |ω|`.
-/
@[simp] def logVorticity (S : MediumState) : ℝ := S.center.logVorticity

/-- Convenience: absolute log-vorticity (magnitude proxy). -/
@[simp] def absLogVorticity (S : MediumState) : ℝ := |S.center.logVorticity|

/-- A very lightweight “helicity proxy” placeholder.

In the LNAL fluids comments, helicity is tracked in an auxiliary slot; the
current domain file does not expose it directly, so we provide a stubbed
field for downstream refinement.
-/
structure HelicityProxy where
  value : ℝ

/-- Attach a helicity proxy to a medium state (display-level wrapper). -/
structure MediumStateH where
  S : MediumState
  H : HelicityProxy

end Medium
end Flight
end IndisputableMonolith

