import IndisputableMonolith.OctaveKernel.VoxelField
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

/-!
# OctaveKernel.Instances.SpatialLattice3D

Concrete, minimal 3D spatial geometry for voxel coupling:

- `Pos N` is a 3D discrete torus (periodic boundary conditions) using `ZMod N`.
- 6 face-neighbor offsets (±x, ±y, ±z) implement first-order adjacency.
- 12 edge-neighbor offsets (±x±y, ±x±z, ±y±z) implement second-order adjacency ("diagonal" channels).

This file does **not** claim these are the only possible couplings. It provides
a canonical geometry object that downstream theorems/simulations can reuse.
-/

namespace IndisputableMonolith
namespace OctaveKernel
namespace Instances

open MeaningfulVoxelField

/-! ## A concrete 3D position space (periodic) -/

/-- A 3D discrete torus position: `(x,y,z)` with wrap-around arithmetic modulo `N`. -/
abbrev Pos (N : ℕ) := (ZMod N) × (ZMod N) × (ZMod N)

namespace Pos

variable {N : ℕ}

/-- Constructor helper for `Pos N`. -/
@[inline] def mk' (x y z : ZMod N) : Pos N := (x, (y, z))

@[inline] def x (p : Pos N) : ZMod N := p.1
@[inline] def y (p : Pos N) : ZMod N := p.2.1
@[inline] def z (p : Pos N) : ZMod N := p.2.2

end Pos

/-! ## Canonical 6 + 12 neighbor offsets -/

namespace Offsets

open Pos

/-- 6 face-neighbor offsets: ±x, ±y, ±z. -/
def face (N : ℕ) : Fin 6 → Pos N
  | ⟨0, _⟩ => mk' (N := N) 1 0 0
  | ⟨1, _⟩ => mk' (N := N) (-1) 0 0
  | ⟨2, _⟩ => mk' (N := N) 0 1 0
  | ⟨3, _⟩ => mk' (N := N) 0 (-1) 0
  | ⟨4, _⟩ => mk' (N := N) 0 0 1
  | ⟨5, _⟩ => mk' (N := N) 0 0 (-1)

/-- 12 edge-neighbor offsets: (±1,±1,0), (±1,0,±1), (0,±1,±1). -/
def edge (N : ℕ) : Fin 12 → Pos N
  | ⟨0, _⟩  => mk' (N := N) 1 1 0
  | ⟨1, _⟩  => mk' (N := N) 1 (-1) 0
  | ⟨2, _⟩  => mk' (N := N) (-1) 1 0
  | ⟨3, _⟩  => mk' (N := N) (-1) (-1) 0
  | ⟨4, _⟩  => mk' (N := N) 1 0 1
  | ⟨5, _⟩  => mk' (N := N) 1 0 (-1)
  | ⟨6, _⟩  => mk' (N := N) (-1) 0 1
  | ⟨7, _⟩  => mk' (N := N) (-1) 0 (-1)
  | ⟨8, _⟩  => mk' (N := N) 0 1 1
  | ⟨9, _⟩  => mk' (N := N) 0 1 (-1)
  | ⟨10, _⟩ => mk' (N := N) 0 (-1) 1
  | ⟨11, _⟩ => mk' (N := N) 0 (-1) (-1)

end Offsets

/-! ## A canonical voxel lattice + stencils on the torus -/

open Pos Offsets

/-- The canonical 3D torus lattice geometry: 6 face neighbors + 12 edge neighbors. -/
def torusVoxelLattice (N : ℕ) : MeaningfulVoxelField.VoxelLattice (Pos N) :=
{ faceSrc := fun p d => p + face N d
  edgeSrc := fun p d => p + edge N d }

/-- Lattice source mappings are bijections (needed for conservation proofs). -/
theorem torusVoxelLattice_face_bijective (N : ℕ) (d : Fin 6) :
    Function.Bijective (fun p : Pos N => (torusVoxelLattice N).faceSrc p d) := by
  have : (fun p : Pos N => (torusVoxelLattice N).faceSrc p d) = (fun p => p + face N d) := rfl
  rw [this]
  exact (Equiv.addRight (face N d)).bijective

theorem torusVoxelLattice_edge_bijective (N : ℕ) (d : Fin 12) :
    Function.Bijective (fun p : Pos N => (torusVoxelLattice N).edgeSrc p d) := by
  have : (fun p : Pos N => (torusVoxelLattice N).edgeSrc p d) = (fun p => p + edge N d) := rfl
  rw [this]
  exact (Equiv.addRight (edge N d)).bijective

/-! ## Track C: Isotropy / Symmetry -/

/-- Face offsets are symmetric under sign flip (±x, ±y, ±z). -/
theorem face_offsets_symmetric (N : ℕ) :
    ∀ d : Fin 6, ∃ d' : Fin 6, face N d' = - (face N d) := by
  intro d; fin_cases d
  · exact ⟨1, by simp [face, mk']⟩
  · exact ⟨0, by simp [face, mk']⟩
  · exact ⟨3, by simp [face, mk']⟩
  · exact ⟨2, by simp [face, mk']⟩
  · exact ⟨5, by simp [face, mk']⟩
  · exact ⟨4, by simp [face, mk']⟩

/-- Face offsets are symmetric under axis permutation (x↔y↔z). -/
theorem face_offsets_perm_symmetric (N : ℕ) :
    ∀ d : Fin 6, ∃ d' : Fin 6, (face N d').x = (face N d).y ∧ (face N d').y = (face N d).z ∧ (face N d').z = (face N d).x := by
  intro d; fin_cases d
  · exact ⟨4, by simp [face, mk', Pos.x, Pos.y, Pos.z]⟩
  · exact ⟨5, by simp [face, mk', Pos.x, Pos.y, Pos.z]⟩
  · exact ⟨0, by simp [face, mk', Pos.x, Pos.y, Pos.z]⟩
  · exact ⟨1, by simp [face, mk', Pos.x, Pos.y, Pos.z]⟩
  · exact ⟨2, by simp [face, mk', Pos.x, Pos.y, Pos.z]⟩
  · exact ⟨3, by simp [face, mk', Pos.x, Pos.y, Pos.z]⟩

/-- Edge offsets are symmetric under sign flip. -/
theorem edge_offsets_symmetric (N : ℕ) :
    ∀ d : Fin 12, ∃ d' : Fin 12, edge N d' = - (edge N d) := by
  intro d; fin_cases d
  · exact ⟨3, by simp [edge, mk']⟩
  · exact ⟨2, by simp [edge, mk']⟩
  · exact ⟨1, by simp [edge, mk']⟩
  · exact ⟨0, by simp [edge, mk']⟩
  · exact ⟨7, by simp [edge, mk']⟩
  · exact ⟨6, by simp [edge, mk']⟩
  · exact ⟨5, by simp [edge, mk']⟩
  · exact ⟨4, by simp [edge, mk']⟩
  · exact ⟨11, by simp [edge, mk']⟩
  · exact ⟨10, by simp [edge, mk']⟩
  · exact ⟨9, by simp [edge, mk']⟩
  · exact ⟨8, by simp [edge, mk']⟩

/-- Edge offsets are symmetric under axis permutation (x↔y↔z). -/
theorem edge_offsets_perm_symmetric (N : ℕ) :
    ∀ d : Fin 12, ∃ d' : Fin 12, (edge N d').x = (edge N d).y ∧ (edge N d').y = (edge N d).z ∧ (edge N d').z = (edge N d).x := by
  intro d; fin_cases d
  · exact ⟨4, by simp [edge, mk', Pos.x, Pos.y, Pos.z]⟩
  · exact ⟨6, by simp [edge, mk', Pos.x, Pos.y, Pos.z]⟩
  · exact ⟨5, by simp [edge, mk', Pos.x, Pos.y, Pos.z]⟩
  · exact ⟨7, by simp [edge, mk', Pos.x, Pos.y, Pos.z]⟩
  · exact ⟨8, by simp [edge, mk', Pos.x, Pos.y, Pos.z]⟩
  · exact ⟨10, by simp [edge, mk', Pos.x, Pos.y, Pos.z]⟩
  · exact ⟨9, by simp [edge, mk', Pos.x, Pos.y, Pos.z]⟩
  · exact ⟨11, by simp [edge, mk', Pos.x, Pos.y, Pos.z]⟩
  · exact ⟨0, by simp [edge, mk', Pos.x, Pos.y, Pos.z]⟩
  · exact ⟨1, by simp [edge, mk', Pos.x, Pos.y, Pos.z]⟩
  · exact ⟨2, by simp [edge, mk', Pos.x, Pos.y, Pos.z]⟩
  · exact ⟨3, by simp [edge, mk', Pos.x, Pos.y, Pos.z]⟩

/-- The canonical (faces + edges) stencil on the torus.

`wFace` is the first-order coupling weight; `wEdge` is the second-order correction weight. -/
noncomputable def torusFacePlusEdgeStencil (N : ℕ) (wFace wEdge : ℂ) :
    MeaningfulVoxelField.SpatialStencil (Pos N) :=
  (MeaningfulVoxelField.VoxelLattice.facePlusEdgeStencil (L := torusVoxelLattice N) wFace wEdge)

end Instances
end OctaveKernel
end IndisputableMonolith
