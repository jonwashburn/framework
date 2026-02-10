import Mathlib

namespace Scratch

open scoped Real
open Complex

noncomputable section

variable (a : ℂ) (B : ℝ)

#check (by
  have : (Complex.exp (B • (-a)) - 1) * (-a)⁻¹ = -((Complex.exp (-( (B:ℂ) * a)) - 1) * a⁻¹) := by
    simp [Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm]
  exact this)

end

end Scratch
