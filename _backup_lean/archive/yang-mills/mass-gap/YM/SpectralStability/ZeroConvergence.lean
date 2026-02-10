import Mathlib

/-!
Trivial norm-convergence baseline: operator norm goes to 0.

Setting:
  • X = ℂ with its standard Hilbert structure
  • Tn := 0 for all n, and T := 0
  • Prove ‖Tn − T‖ → 0 in operator norm

Result:
  • opNorm_converges_zero_scalar
-/

namespace YM.SpectralStability.ZeroConvergence

open Complex

abbrev Operator := ℂ →L[ℂ] ℂ

/-- Constant zero operator family. -/
def Tn (n : ℕ) : Operator := 0

/-- Zero limit operator. -/
def Tlim : Operator := 0

/-- The zero operators converge in operator norm (trivially): ‖Tₙ − T‖ = 0. -/
theorem opNorm_converges_zero_scalar :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, ‖Tn n - Tlim‖ ≤ ε := by
  intro ε hε
  refine ⟨0, ?_⟩
  intro n _
  -- (Tn n − Tlim) = 0, so the op norm is 0 ≤ ε
  have : (Tn n - Tlim : Operator) = 0 := by simp [Tn, Tlim]
  simpa [this]  -- ‖0‖ = 0 ≤ ε

end YM.SpectralStability.ZeroConvergence
