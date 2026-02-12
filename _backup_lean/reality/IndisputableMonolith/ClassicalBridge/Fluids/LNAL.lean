import Mathlib
import IndisputableMonolith.LNAL.VM

namespace IndisputableMonolith
namespace ClassicalBridge
namespace Fluids

/-!
# Fluids Bridge: LNAL spatial interface

The existing LNAL core (`IndisputableMonolith/LNAL/VM.lean`) defines the single-voxel VM.
For fluids we need a **spatial** semantics (a whole field of voxels).

This file defines a minimal, *bridge-local* interface:

- the spatial state is an array of `(Reg6 × Aux5)` voxels
- a `SpatialSemantics` gives a one-step update given an `LProgram`.

We keep this separate from `LNAL/MultiVoxelVM.lean` so the bridge can evolve without
pulling in any experimental multi-voxel infrastructure.
-/

abbrev LNALVoxel : Type := IndisputableMonolith.LNAL.Reg6 × IndisputableMonolith.LNAL.Aux5
abbrev LNALField : Type := Array LNALVoxel

/-- A minimal interface for spatial execution of an LNAL program over a field of voxels. -/
structure SpatialSemantics where
  step : IndisputableMonolith.LNAL.LProgram → LNALField → LNALField

namespace SpatialSemantics

/-- Iterate `step` for `n` steps (functional execution). -/
def run (sem : SpatialSemantics) (P : IndisputableMonolith.LNAL.LProgram) : LNALField → Nat → LNALField
  | s, 0 => s
  | s, Nat.succ n => run sem P (sem.step P s) n

end SpatialSemantics

end Fluids
end ClassicalBridge
end IndisputableMonolith
