import IndisputableMonolith.OctaveKernel.Instances.ConsciousnessLayer

namespace Scratch
open IndisputableMonolith.OctaveKernel.Instances
open IndisputableMonolith.Constants

example (theta1 theta2 : PhaseValue) (k : ℕ) :
    phase_coupling theta1 theta2 (k + 1) =
      Real.cos (2 * Real.pi * (theta1.val - theta2.val)) * (phi ^ (-(↑k : ℝ) - 1)) := by
  -- unfold and normalize casts
  simp [phase_coupling, Nat.cast_add_one, Int.cast_add, Int.cast_one, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
