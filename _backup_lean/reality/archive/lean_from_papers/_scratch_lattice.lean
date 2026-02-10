import Mathlib
import IndisputableMonolith.LNAL.MultiVoxelVM

namespace IndisputableMonolith
namespace LNAL

open Lattice3D

theorem neighbors_symmetric_proof (lat : Lattice3D) :
    ∀ i j, j ∈ lat.neighbors i → i ∈ lat.neighbors j := by
  intro i j hj
  unfold neighbors at hj ⊢
  rcases h_id : lat.fromVoxelId i with ⟨xi, yi, zi⟩
  simp only [List.mem_cons, List.mem_nil, or_false] at hj
  -- Handle the case where j is the +x neighbor of i
  rcases hj with h | h | h | h | h | h
  · -- j = lat.toVoxelId ((xi + 1) % lat.nx) yi zi
    subst h
    -- Need to show i ∈ neighbors j
    -- fromVoxelId j should be ((xi+1)%nx, yi, zi)
    -- and its -x neighbor should be toVoxelId (if (xi+1)%nx = 0 then nx-1 else (xi+1)%nx - 1) yi zi
    -- which is i.
    sorry
  all_goals { sorry }

end LNAL
end IndisputableMonolith
