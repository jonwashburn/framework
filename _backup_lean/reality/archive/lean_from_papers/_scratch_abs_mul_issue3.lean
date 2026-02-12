import IndisputableMonolith.OctaveKernel.Instances.ConsciousnessLayer

namespace Scratch
open IndisputableMonolith.OctaveKernel.Instances
open IndisputableMonolith.Constants

variable (theta1 theta2 : PhaseValue) (k : ℕ)

example : |Real.cos (2 * Real.pi * (theta1.val - theta2.val)) * (phi ^ (-(↑(k + 1) : ℝ)))|
      = |Real.cos (2 * Real.pi * (theta1.val - theta2.val))| * |phi ^ (-(↑(k + 1) : ℝ))| := by
  simpa [abs_mul]

end Scratch
