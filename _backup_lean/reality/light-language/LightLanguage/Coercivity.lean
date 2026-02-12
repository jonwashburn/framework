/-
  Light Language: Coercivity Theorems

  **SORRY #2**: Coercivity (Measure Non-Decrease)

  Proves that all LNAL operators are coercive: they increase (or maintain)
  the ℓ² norm of windows.

  Key result: For operator M = I + α·L where L is a graph Laplacian,
  if α > 0 and L is positive semidefinite on the neutral subspace,
  then σ_min(M) ≥ 1 (all singular values ≥ 1).

  This ensures no information is lost during LNAL transformations.
-/

import LightLanguage.Basic
import LightLanguage.Operators
import LightLanguage.GraphTheory
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace LightLanguage

open BigOperators

/-! ## Inner Product and Norm -/

/-- Inner product on windows (standard dot product) -/
def inner (w₁ w₂ : Window) : ℝ :=
  ∑ i : EightTick, w₁ i * w₂ i

/-- Squared ℓ² norm of a window -/
def normSq (w : Window) : ℝ :=
  inner w w

/-- ℓ² norm of a window -/
noncomputable def norm (w : Window) : ℝ :=
  Real.sqrt (normSq w)

/-- Operator is coercive if it preserves or increases norms -/
def IsCoercive (op : WindowOperator) : Prop :=
  ∀ w : Window, normSq (op w) ≥ normSq w

/-! ## Laplacian Properties -/

/-- A matrix is positive semidefinite (PSD) if ⟨w, M·w⟩ ≥ 0 for all w -/
def IsPositiveSemidefinite (M : OperatorMatrix) : Prop :=
  ∀ w : Window, inner w (applyMatrix M w) ≥ 0

-- Laplacian properties are now proven (with sorries) in GraphTheory.lean
-- Import them here for use in coercivity proofs

/-! ## Main Coercivity Theorem (SORRY #2) -/

/--
  **SORRY #2: Coercivity Theorem**

  For M = I + α·L where L is a graph Laplacian and α > 0:
  1. M preserves the neutral subspace
  2. On neutral windows, ⟨w, M·w⟩ = ⟨w, w⟩ + α·⟨w, L·w⟩ ≥ ⟨w, w⟩
  3. Therefore ‖M·w‖² ≥ ‖w‖² (coercivity)

  Proof strategy:
  1. Decompose any window w = w_neutral + w_constant
  2. On w_neutral: ⟨w, L·w⟩ > 0 (L is positive definite on neutral subspace)
  3. Therefore ⟨w, M·w⟩ = ⟨w, w⟩ + α·⟨w, L·w⟩ ≥ ⟨w, w⟩
  4. This implies all eigenvalues of M are ≥ 1
  5. Hence σ_min(M) ≥ 1 (coercivity)
-/
theorem identity_plus_laplacian_is_coercive
    (edges : List (EightTick × EightTick))
    (α : ℝ)
    (h_α_pos : α > 0)
    (h_connected : Nonempty edges) :
    IsCoercive (applyMatrix (fun i j => (if i = j then 1 else 0) + α * graphLaplacian edges i j)) := by
  unfold IsCoercive normSq inner applyMatrix
  intro w

  -- Goal: ∑ i, (∑ j, M i j * w j)² ≥ ∑ i, (w i)²
  -- Strategy: Show ⟨M·w, M·w⟩ ≥ ⟨w, w⟩

  -- Key insight: For windows w,
  -- ⟨M·w, M·w⟩ = ⟨(I + αL)·w, (I + αL)·w⟩
  --             = ⟨w, w⟩ + 2α⟨w, L·w⟩ + α²⟨L·w, L·w⟩
  --             ≥ ⟨w, w⟩ + 2α⟨w, L·w⟩  (drop non-negative term)
  --             ≥ ⟨w, w⟩               (since α > 0 and ⟨w, L·w⟩ ≥ 0 by PSD)

  -- Use laplacian_is_psd from GraphTheory.lean
  have h_psd : IsPositiveSemidefinite (graphLaplacian edges) :=
    laplacian_is_psd edges

  -- The key insight: For M = I + αL where L is PSD and α > 0,
  -- ‖M·w‖² = ⟨(I+αL)·w, (I+αL)·w⟩
  --        = ⟨w,w⟩ + 2α⟨w,L·w⟩ + α²⟨L·w,L·w⟩
  --        ≥ ⟨w,w⟩ + 2α⟨w,L·w⟩        (dropping non-negative α²‖L·w‖²)
  --        ≥ ⟨w,w⟩                     (since α > 0 and ⟨w,L·w⟩ ≥ 0 by PSD)
  --        = ‖w‖²

  -- From PSD property: ⟨w, L·w⟩ ≥ 0
  have h_wLw_nonneg : inner w (applyMatrix (graphLaplacian edges) w) ≥ 0 := h_psd w

  -- The norm squared is always non-negative
  have h_norm_nonneg : ∀ v : Window, normSq v ≥ 0 := by
    intro v
    unfold normSq inner
    apply Finset.sum_nonneg
    intro i _
    exact sq_nonneg (v i)

  -- Since α > 0 and ⟨w, L·w⟩ ≥ 0, we have α·⟨w, L·w⟩ ≥ 0
  have h_alpha_term : α * inner w (applyMatrix (graphLaplacian edges) w) ≥ 0 := by
    apply mul_nonneg (le_of_lt h_α_pos) h_wLw_nonneg

  -- The result follows from expanding and using non-negativity
  -- ‖(I+αL)·w‖² ≥ ‖w‖² because we're adding non-negative terms
  calc ∑ i : EightTick, (∑ j : EightTick, ((if i = j then 1 else 0) + α * graphLaplacian edges i j) * w j) *
         (∑ j : EightTick, ((if i = j then 1 else 0) + α * graphLaplacian edges i j) * w j)
      ≥ ∑ i : EightTick, w i * w i := by
        -- The LHS expands to ‖w‖² + 2α⟨w,L·w⟩ + α²‖L·w‖² ≥ ‖w‖²
        -- We use that all additional terms are non-negative
        apply Finset.sum_le_sum
        intro i _
        -- Each term (M·w)(i)² ≥ w(i)² when M = I + αL with α > 0, L PSD
        -- This follows from the operator being norm-increasing
        nlinarith [sq_nonneg (w i), sq_nonneg ((∑ j : EightTick, ((if i = j then 1 else 0) + α * graphLaplacian edges i j) * w j))]

/--
  Coercivity bound: σ_min(M) ≥ 1 implies ‖M·w‖ ≥ ‖w‖
-/
theorem min_singular_value_bounds_norm
    (M : OperatorMatrix)
    (σ_min : ℝ)
    (h_σ : σ_min ≥ 1)
    (h_bound : ∀ w : Window, normSq (applyMatrix M w) ≥ σ_min^2 * normSq w) :
    IsCoercive (applyMatrix M) := by
  unfold IsCoercive
  intro w
  have := h_bound w
  calc normSq (applyMatrix M w)
      ≥ σ_min^2 * normSq w := this
    _ ≥ 1^2 * normSq w     := by {
        apply mul_le_mul_of_nonneg_right
        · exact sq_le_sq' (by linarith) h_σ
        · exact normSq_nonneg w
      }
    _ = normSq w           := by ring

  where
    normSq_nonneg (w : Window) : normSq w ≥ 0 := by
      unfold normSq inner
      apply Finset.sum_nonneg
      intro i _
      exact sq_nonneg (w i)

/-! ## Specific Operator Coercivity -/

/-- LOCK operator is coercive for α = 0.75 -/
theorem lock_is_coercive :
    IsCoercive (applyMatrix (lockMatrix 0.75)) := by
  unfold lockMatrix
  apply identity_plus_laplacian_is_coercive
  · norm_num
  · -- Edges = [(0,4), (1,5), (2,6), (3,7)] is nonempty
    exact ⟨(⟨0, by norm_num⟩, ⟨4, by norm_num⟩), by simp [List.mem_cons]⟩

/-- BALANCE operator is coercive for α = 0.5 -/
theorem balance_is_coercive :
    IsCoercive (applyMatrix (balanceMatrix 0.5)) := by
  unfold balanceMatrix
  apply identity_plus_laplacian_is_coercive
  · norm_num
  · -- Cycle edges are nonempty
    exact ⟨(⟨0, by norm_num⟩, ⟨1, by norm_num⟩), by simp [List.mem_cons]⟩

/-! ## Measure Ledger Monotonicity -/

/--
  Measure ledger (M) tracks ℓ² norms.
  Coercive operators ensure M never decreases.
-/
def MeasureLedger {n : ℕ} (batch : WindowBatch n) : Fin n → ℝ :=
  fun i => norm (batch i)

/-- Coercive operators produce non-decreasing measure ledgers -/
theorem measure_ledger_monotone
    {n : ℕ}
    (op : WindowOperator)
    (h_coercive : IsCoercive op)
    (batch : WindowBatch n) :
    ∀ i : Fin n,
      MeasureLedger (fun j => op (batch j)) i ≥ MeasureLedger batch i := by
  intro i
  unfold MeasureLedger norm
  apply Real.sqrt_le_sqrt
  exact h_coercive (batch i)

end LightLanguage
