import IndisputableMonolith.OctaveKernel.Instances.ConsciousnessLayer

namespace Scratch
open IndisputableMonolith.OctaveKernel.Instances
open IndisputableMonolith.Constants

variable (theta1 theta2 : PhaseValue) (k : ℕ)

example :
    let c : ℝ := Real.cos (2 * Real.pi * (theta1.val - theta2.val))
    |c * (phi ^ (-(↑(k + 1) : ℝ)))| = |c| * (phi ^ (-(↑(k + 1) : ℝ))) := by
  intro c
  have hphi_nonneg : 0 ≤ phi := le_of_lt phi_pos
  have hpow1_nonneg : 0 ≤ phi ^ (-(↑(k + 1) : ℝ)) := Real.rpow_nonneg hphi_nonneg _
  calc
    |c * (phi ^ (-(↑(k + 1) : ℝ)))|
        = |c| * |phi ^ (-(↑(k + 1) : ℝ))| := by
            simpa [abs_mul]
    _ = |c| * (phi ^ (-(↑(k + 1) : ℝ))) := by
            simp [abs_of_nonneg hpow1_nonneg]

end Scratch
