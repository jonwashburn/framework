/-
  Light Language: Operator Theorems

  Proves that LNAL operators (LOCK, BALANCE, FOLD, BRAID) preserve neutrality.

  **SORRY #1**: Neutrality Preservation Theorem

  Main result: If a matrix M has all column sums equal to 1, then applying M
  to any neutral window produces a neutral window.

  This is the foundational property ensuring ledger balance is maintained
  through all LNAL transformations.
-/

import LightLanguage.Basic
import LightLanguage.GraphTheory
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Basic

namespace LightLanguage

open BigOperators

/-! ## Main Neutrality Theorem (SORRY #1) -/

/--
  **SORRY #1: Neutrality Preservation**

  If a matrix M has all column sums equal to 1, then it preserves neutrality.

  Proof strategy:
  1. For neutral window w, we have ∑ᵢ w(i) = 0
  2. Applying M: (M·w)(i) = ∑ⱼ M(i,j) · w(j)
  3. Sum over rows: ∑ᵢ (M·w)(i) = ∑ᵢ ∑ⱼ M(i,j) · w(j)
  4. Swap sum order: = ∑ⱼ (∑ᵢ M(i,j)) · w(j)
  5. Column sum = 1: = ∑ⱼ 1 · w(j) = ∑ⱼ w(j) = 0 ✓
-/
theorem neutrality_preserved_by_column_sum_one
    (M : OperatorMatrix)
    (h_col : AllColumnSumsOne M) :
    PreservesNeutrality (applyMatrix M) := by
  unfold PreservesNeutrality IsNeutral windowSum applyMatrix
  intro w hw
  -- Goal: ∑ i, (∑ j, M i j * w j) = 0
  -- Given: ∑ i, w i = 0

  -- Swap the order of summation
  conv_lhs =>
    rw [Finset.sum_comm]

  -- Now have: ∑ j, (∑ i, M i j * w j)
  -- Factor out w j
  simp only [← Finset.mul_sum]

  -- Now have: ∑ j, (∑ i, M i j) * w j
  -- Use column sum hypothesis
  conv_lhs =>
    arg 2
    intro j
    rw [← h_col j]  -- Replace ∑ i, M i j with columnSum M j = 1

  -- Now have: ∑ j, 1 * w j = ∑ j, w j = 0 by hw
  simp only [one_mul]
  exact hw

/-! ## Operator Construction Lemmas -/

/--
  Graph Laplacian construction.

  For an undirected graph with edges, the Laplacian L satisfies:
  - L(i,i) = degree(i)
  - L(i,j) = -1 if (i,j) is an edge
  - L(i,j) = 0 otherwise
-/
def graphLaplacian (edges : List (EightTick × EightTick)) : OperatorMatrix :=
  fun i j =>
    if i = j then
      -- Diagonal: count edges incident to i
      (edges.filter (fun e => e.1 = i ∨ e.2 = i)).length
    else
      -- Off-diagonal: -1 if edge exists, 0 otherwise
      if (i, j) ∈ edges ∨ (j, i) ∈ edges then -1 else 0

/--
  LOCK operator matrix: I + α·L where L is Laplacian on edges {(0,4), (1,5), (2,6), (3,7)}
-/
def lockMatrix (α : ℝ) : OperatorMatrix :=
  let edges : List (EightTick × EightTick) := [
    (⟨0, by norm_num⟩, ⟨4, by norm_num⟩),
    (⟨1, by norm_num⟩, ⟨5, by norm_num⟩),
    (⟨2, by norm_num⟩, ⟨6, by norm_num⟩),
    (⟨3, by norm_num⟩, ⟨7, by norm_num⟩)
  ]
  let L := graphLaplacian edges
  fun i j => (if i = j then 1 else 0) + α * L i j

/--
  BALANCE operator matrix: I + α·L where L is Laplacian on cycle C₈
-/
def balanceMatrix (α : ℝ) : OperatorMatrix :=
  let edges : List (EightTick × EightTick) := [
    (⟨0, by norm_num⟩, ⟨1, by norm_num⟩),
    (⟨1, by norm_num⟩, ⟨2, by norm_num⟩),
    (⟨2, by norm_num⟩, ⟨3, by norm_num⟩),
    (⟨3, by norm_num⟩, ⟨4, by norm_num⟩),
    (⟨4, by norm_num⟩, ⟨5, by norm_num⟩),
    (⟨5, by norm_num⟩, ⟨6, by norm_num⟩),
    (⟨6, by norm_num⟩, ⟨7, by norm_num⟩),
    (⟨7, by norm_num⟩, ⟨0, by norm_num⟩)
  ]
  let L := graphLaplacian edges
  fun i j => (if i = j then 1 else 0) + α * L i j

/-! ## Column Sum Verification for Specific Operators -/

/-- I + α·L has column sums equal to 1 (since L has column sum 0) -/
lemma identity_plus_laplacian_column_sum_one
    (edges : List (EightTick × EightTick)) (α : ℝ) :
    AllColumnSumsOne (fun i j => (if i = j then 1 else 0) + α * graphLaplacian edges i j) := by
  unfold AllColumnSumsOne columnSum
  intro j
  -- Sum over column j: ∑ i, (δᵢⱼ + α·L(i,j))
  --                  = ∑ i, δᵢⱼ + α·∑ i, L(i,j)
  --                  = 1 + α·0 = 1
  rw [Finset.sum_add_distrib]
  simp only [Finset.mul_sum]
  -- First sum: ∑ i, δᵢⱼ = 1
  have h1 : ∑ i : EightTick, (if i = j then 1 else 0 : ℝ) = 1 := by
    -- Only i=j contributes 1, all others contribute 0
    -- This is the definition of the identity matrix column sum
    have : (Finset.univ.filter (fun i => i = j)).card = 1 := by
      simp [Finset.filter_eq', Finset.card_singleton]
    calc ∑ i : EightTick, (if i = j then 1 else 0 : ℝ)
        = ∑ i in Finset.univ.filter (fun i => i = j), (1 : ℝ) := by
          apply Finset.sum_filter
          intro i
          split_ifs with h
          · exact one_ne_zero
          · exact rfl
      _ = ((Finset.univ.filter (fun i => i = j)).card : ℝ) := by
          exact Finset.sum_const (1 : ℝ)
      _ = (1 : ℝ) := by
          rw [this]
          norm_num
  -- Second sum: ∑ i, L(i,j) = 0
  have h2 : ∑ i : EightTick, graphLaplacian edges i j = 0 := by
    exact laplacian_column_sum_zero edges j
  rw [h1, h2]
  ring

/-- LOCK preserves neutrality for α = 0.75 (calibrated value from Python implementation) -/
theorem lock_preserves_neutrality :
    PreservesNeutrality (applyMatrix (lockMatrix 0.75)) := by
  apply neutrality_preserved_by_column_sum_one
  exact identity_plus_laplacian_column_sum_one _ 0.75

/-- BALANCE preserves neutrality for α = 0.5 -/
theorem balance_preserves_neutrality :
    PreservesNeutrality (applyMatrix (balanceMatrix 0.5)) := by
  apply neutrality_preserved_by_column_sum_one
  exact identity_plus_laplacian_column_sum_one _ 0.5

/-! ## Batch Operations -/

/-- Applying an operator to a batch of neutral windows yields neutral windows -/
theorem batch_neutrality_preserved
    {n : ℕ}
    (M : OperatorMatrix)
    (h_col : AllColumnSumsOne M)
    (batch : WindowBatch n)
    (h_neutral : BatchIsNeutral batch) :
    BatchIsNeutral (fun i => applyMatrix M (batch i)) := by
  unfold BatchIsNeutral at *
  intro i
  apply neutrality_preserved_by_column_sum_one M h_col
  exact h_neutral i

end LightLanguage
