import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.RSBridge.Anchor

namespace IndisputableMonolith.Physics.PMNS

open Constants

/-- The PMNS mixing weights follow the Born rule over the ladder steps.
    Weight W_ij = exp(-Δτ_ij * J_bit) = φ^-Δτ_ij. -/
noncomputable def pmns_weight (dτ : ℤ) : ℝ :=
  Real.exp (- (dτ : ℝ) * J_bit)

/-- **DEFINITION: PMNS Unitarity Forcing**
    The 8-tick closure cycle forces the mixing matrix to be unitary by preserving
    the total recognition probability across a cycle. -/
structure PMNSUnitarity (U : Matrix (Fin 3) (Fin 3) ℂ) : Prop where
  unitary : Matrix.IsUnitary U
  matches_weights : ∀ i j, (Complex.abs (U i j)) ^ 2 =
    pmns_weight (IndisputableMonolith.RSBridge.rung (match i with | 0 => .nu1 | 1 => .nu2 | 2 => .nu3) -
                 IndisputableMonolith.RSBridge.rung (match j with | 0 => .nu1 | 1 => .nu2 | 2 => .nu3)) / 3

end IndisputableMonolith.Physics.PMNS
