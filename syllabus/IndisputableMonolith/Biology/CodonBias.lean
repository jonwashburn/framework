import Mathlib
import IndisputableMonolith/Compat

open Real Complex
open scoped BigOperators Matrix

/-!
Codon usage bias proxy (throughput vs fidelity positivity).

We model throughput as `1/(n+1)` for a message length `n` and
fidelity as `exp(-e)` for error level `e`. The resulting bias is
strictly positive for all inputs, providing a minimal compiling
statement for certificates and reports.
-/

namespace IndisputableMonolith
namespace Biology
namespace CodonBias

noncomputable def throughput (n : Nat) : ℝ := 1 / (n.succ : ℝ)

noncomputable def fidelity (e : ℝ) : ℝ := Real.exp (- e)

noncomputable def bias (n : Nat) (e : ℝ) : ℝ := throughput n / fidelity e

/-- Bias is strictly positive for all lengths `n` and error levels `e`. -/
theorem bias_opt (n : Nat) (e : ℝ) : bias n e > 0 := by
  dsimp [bias, throughput, fidelity]
  have hden_pos : 0 < (n.succ : ℝ) := by exact_mod_cast Nat.succ_pos n
  have hthrough : 0 < 1 / (n.succ : ℝ) := by
    simpa [one_div] using (inv_pos.mpr hden_pos : 0 < ((n.succ : ℝ))⁻¹)
  have hfidel : 0 < Real.exp (- e) := Real.exp_pos _
  exact div_pos hthrough hfidel

end CodonBias
end Biology
end IndisputableMonolith
