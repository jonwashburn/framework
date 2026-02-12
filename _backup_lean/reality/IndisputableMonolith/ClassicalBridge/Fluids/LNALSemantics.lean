import Mathlib.Data.Fintype.Basic
import IndisputableMonolith.ClassicalBridge.Fluids.LNAL
import IndisputableMonolith.ClassicalBridge.Fluids.Galerkin2D

namespace IndisputableMonolith.ClassicalBridge.Fluids

open Real
open scoped InnerProductSpace

/-!
# LNALSemantics (Milestone M2)

This file provides:
- a minimal **spatial** semantics for running an LNAL program over an `LNALField`
  (an `Array (Reg6 × Aux5)`), and
- an explicit **encoding** of the 2D Galerkin Fourier state (`Galerkin2D`) into LNAL voxels.

This is intentionally minimal (no neighbor graph / no coupling between voxels yet).
-/

namespace LNALSemantics

open IndisputableMonolith.LNAL

/-- One-voxel execution: run a single LNAL step on a `(Reg6 × Aux5)` voxel. -/
def voxelStep (P : LProgram) (v : LNALVoxel) : LNALVoxel :=
  let s0 : LState := LState.init v.1 v.2
  let s1 : LState := lStep P s0
  (s1.reg6, s1.aux5)

/-- Minimal spatial semantics: voxels evolve independently (no neighbor interaction yet). -/
def independent : SpatialSemantics :=
  { step := fun P field => field.map (voxelStep P) }

/-- A trivial "do nothing" LNAL program: `LISTEN noop` at every instruction pointer. -/
@[simp] def listenNoopProgram : LProgram :=
  fun _ => LInstr.listen ListenMode.noop

@[simp] lemma voxelStep_listenNoopProgram (v : LNALVoxel) :
    voxelStep listenNoopProgram v = v := by
  rcases v with ⟨r6, a5⟩
  simp [voxelStep, listenNoopProgram, lStep]

@[simp] lemma independent_step_listenNoopProgram (field : LNALField) :
    independent.step listenNoopProgram field = field := by
  -- `LISTEN noop` does not change `(reg6, aux5)` for any voxel, so the spatial step is `Array.map id`.
  simpa [independent] using
    (Array.map_id'' (f := voxelStep listenNoopProgram) (h := by intro v; simp) field)

end LNALSemantics

namespace Encoding

open IndisputableMonolith.LNAL

/-!
## Encoding Galerkin2D → LNALField
-/

/-- Quantize a real coefficient to an integer magnitude (very coarse; placeholder for later). -/
noncomputable def coeffMag (x : ℝ) : Int :=
  Int.floor |x|

/-- A sign/parity encoding for a real coefficient. -/
noncomputable def coeffSign (x : ℝ) : Int :=
  if x < 0 then (-1) else 1

/-- Encode a single Galerkin coefficient (at one Fourier mode and one component) into an LNAL voxel. -/
noncomputable def encodeIndex {N : ℕ} (u : GalerkinState N) (i : (modes N) × Fin 2) : LNALVoxel :=
  let k : Mode2 := (i.1 : Mode2)
  let x : ℝ := u i
  let r6 : Reg6 :=
    { nuPhi := coeffMag x
      ell := k.1
      sigma := coeffSign x
      tau := k.2
      kPerp := Int.ofNat i.2.val
      phiE := decide (x < 0) }
  (r6, Aux5.zero)

/-- Encode an entire 2D Galerkin state into an `LNALField`.

We use `Fintype.equivFin` to give a deterministic indexing of the finite coefficient set
`(modes N) × Fin 2`, then store one coefficient per voxel.
-/
noncomputable def encodeGalerkin2D {N : ℕ} (u : GalerkinState N) : LNALField :=
  let e : Fin (Fintype.card ((modes N) × Fin 2)) ≃ ((modes N) × Fin 2) :=
    (Fintype.equivFin ((modes N) × Fin 2)).symm
  Array.ofFn (fun j => encodeIndex u (e j))

end Encoding

end IndisputableMonolith.ClassicalBridge.Fluids
