import IndisputableMonolith.OctaveKernel.Instances.ConsciousnessLayer

namespace Scratch
open IndisputableMonolith.OctaveKernel.Instances
open IndisputableMonolith.Constants

variable (theta1 theta2 : PhaseValue) (k : ℕ)

example :
    let c : ℝ := Real.cos (2 * Real.pi * (theta1.val - theta2.val))
    |c * (phi ^ (-(↑(k + 1) : ℝ)))| = |c| * |phi ^ (-(↑(k + 1) : ℝ))| := by
  intro c
  exact abs_mul c (phi ^ (-(↑(k + 1) : ℝ)))

end Scratch
