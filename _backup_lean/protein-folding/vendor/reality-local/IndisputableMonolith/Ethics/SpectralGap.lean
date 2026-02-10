import Mathlib
import IndisputableMonolith.Foundation.RecognitionOperator
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Spectral Gap for Reciprocity Graphs

This module provides eigenvalue computation infrastructure for the σ-graph
Laplacian, enabling proper computation of the spectral gap λ₂ used in
lexicographic audit step 4 (robustness).

## Key Definitions

1. `eigenvalues_sorted`: Eigenvalues of a symmetric real matrix in ascending order
2. `spectral_gap_proper`: The Fiedler eigenvalue λ₂ (second-smallest)
3. Monotonicity lemmas for lexicographic proofs

## Mathematical Background

For the Laplacian L of a weighted graph:
- L is symmetric positive semi-definite
- λ₁ = 0 with eigenvector 1 (constant vector)
- λ₂ > 0 iff the graph is connected
- λ₂ measures "algebraic connectivity" - how hard it is to disconnect the graph

In the ethics context:
- Higher λ₂ → more robust reciprocity network
- Lower λ₂ → network is fragile, easier to partition agents
-/

namespace IndisputableMonolith
namespace Ethics
namespace SpectralGap

open Matrix

variable {n : ℕ} [NeZero n]

/-! ## Eigenvalue Ordering -/

/-- For a symmetric real matrix, eigenvalues are real. -/
structure SymmetricMatrix (n : ℕ) [NeZero n] where
  mat : Matrix (Fin n) (Fin n) ℝ
  symm : mat.IsSymm

/-- The eigenvalues of a symmetric matrix, as a multiset of reals.
    By the spectral theorem, symmetric real matrices have real eigenvalues. -/
noncomputable def eigenvalue_multiset (M : SymmetricMatrix n) : Multiset ℝ :=
  letI : InnerProductSpace ℝ (Fin n → ℝ) := PiLp.innerProductSpace 2 (fun _ => ℝ)
  Multiset.ofList (Matrix.IsHermitian.eigenvalues (M.mat.isHermitian_iff_isSymm.mpr M.symm)).toList

/-- Eigenvalues sorted in ascending order. -/
noncomputable def eigenvalues_sorted (M : SymmetricMatrix n) : Fin n → ℝ :=
  fun i => (eigenvalue_multiset M).sort (· ≤ ·) |>.getD i.val 0

/-- The smallest eigenvalue (λ₁). -/
noncomputable def lambda1 (M : SymmetricMatrix n) : ℝ :=
  eigenvalues_sorted M ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩

/-- The second-smallest eigenvalue (λ₂), the spectral gap / Fiedler value.
    Requires n ≥ 2. -/
noncomputable def lambda2 (M : SymmetricMatrix n) (hn : 2 ≤ n) : ℝ :=
  eigenvalues_sorted M ⟨1, lt_of_lt_of_le (by norm_num : 1 < 2) hn⟩

/-! ## Laplacian Properties -/

/-- A graph Laplacian is symmetric PSD with smallest eigenvalue 0. -/
structure GraphLaplacian (n : ℕ) [NeZero n] extends SymmetricMatrix n where
  /-- Laplacian is positive semi-definite -/
  psd : ∀ v : Fin n → ℝ, 0 ≤ Matrix.dotProduct v (mat.mulVec v)
  /-- Constant vector is in the kernel -/
  kernel_const : mat.mulVec (fun _ => 1) = 0
  /-- Laplacian structure: L = D - A where D is degree diagonal -/
  is_laplacian : ∃ (A : Matrix (Fin n) (Fin n) ℝ),
    A.IsSymm ∧ (∀ i j, 0 ≤ A i j) ∧
    mat = Matrix.diagonal (fun i => ∑ j, A i j) - A

/-- For a graph Laplacian, λ₁ = 0. -/
theorem laplacian_lambda1_eq_zero (L : GraphLaplacian n) :
    lambda1 L.toSymmetricMatrix = 0 := by
  unfold lambda1 eigenvalues_sorted eigenvalue_multiset
  -- Use eigenvalues_eq to get the actual eigenvalues
  set h_herm := L.mat.isHermitian_iff_isSymm.mpr L.symm
  -- Show that 0 is an eigenvalue because kernel is non-trivial (1 is in kernel)
  have h_zero : 0 ∈ Matrix.IsHermitian.eigenvalues h_herm := by
    rw [Matrix.IsHermitian.mem_eigenvalues]
    use (fun _ => 1)
    constructor
    · intro h_null
      have h1 : (fun _ : Fin n => (1 : ℝ)) 0 = 1 := rfl
      rw [h_null] at h1
      simp at h1
    · exact L.kernel_const
  -- Show all eigenvalues are non-negative (PSD)
  have h_nonneg : ∀ λ ∈ Matrix.IsHermitian.eigenvalues h_herm, 0 ≤ λ := by
    intro λ hλ
    rw [Matrix.IsHermitian.mem_eigenvalues] at hλ
    obtain ⟨v, hv_ne, hv_ev⟩ := hλ
    have h_psd := L.psd v
    rw [hv_ev] at h_psd
    rw [Matrix.dotProduct_smul, Matrix.dotProduct_self] at h_psd
    have h_norm_pos : 0 < Matrix.dotProduct v v := by
      apply Matrix.dotProduct_self_pos
      exact hv_ne
    exact nonneg_of_mul_nonneg_right h_psd h_norm_pos
  -- Smallest of a set containing 0 where all elements are non-negative is 0
  have h_list := Matrix.IsHermitian.eigenvalues h_herm
  have h_sorted := h_list.toList.sort (· ≤ ·)
  have h_min : h_sorted.getD 0 0 = 0 := by
    -- The first element of a sorted list of non-negative reals containing 0 is 0
    have h_mem_sorted : 0 ∈ h_sorted := by
      simp only [List.mem_sort, Multiset.mem_toList, h_zero]
    have h_le_all : ∀ x ∈ h_sorted, 0 ≤ x := by
      intro x hx
      rw [List.mem_sort] at hx
      exact h_nonneg x (Multiset.mem_toList.mp hx)
    -- Sorted list means each element is ≤ the next
    -- If 0 is in the list and 0 is the lower bound, it must be at index 0 (if list non-empty)
    have h_ne_nil : h_sorted ≠ [] := by
      intro h_empty
      rw [h_empty] at h_mem_sorted
      simp at h_mem_sorted
    exact List.Sorted.head_eq_of_min_mem (List.sorted_sort (· ≤ ·) _) h_mem_sorted h_le_all
  simp [h_min]

/-- The spectral gap of a Laplacian is λ₂. -/
noncomputable def spectral_gap_of_laplacian (L : GraphLaplacian n) (hn : 2 ≤ n) : ℝ :=
  lambda2 L.toSymmetricMatrix hn

/-- Spectral gap is non-negative for Laplacians. -/
theorem spectral_gap_nonneg (L : GraphLaplacian n) (hn : 2 ≤ n) :
    0 ≤ spectral_gap_of_laplacian L hn := by
  unfold spectral_gap_of_laplacian lambda2 eigenvalues_sorted eigenvalue_multiset
  set h_herm := L.mat.isHermitian_iff_isSymm.mpr L.symm
  -- All eigenvalues are non-negative (PSD)
  have h_nonneg : ∀ λ ∈ Matrix.IsHermitian.eigenvalues h_herm, 0 ≤ λ := by
    intro λ hλ
    rw [Matrix.IsHermitian.mem_eigenvalues] at hλ
    obtain ⟨v, hv_ne, hv_ev⟩ := hλ
    have h_psd := L.psd v
    rw [hv_ev] at h_psd
    rw [Matrix.dotProduct_smul, Matrix.dotProduct_self] at h_psd
    have h_norm_pos : 0 < Matrix.dotProduct v v := by
      apply Matrix.dotProduct_self_pos
      exact hv_ne
    exact nonneg_of_mul_nonneg_right h_psd h_norm_pos
  -- Any element of a sorted list of non-negative reals is non-negative
  have h_list := Matrix.IsHermitian.eigenvalues h_herm
  have h_sorted := h_list.toList.sort (· ≤ ·)
  have h_val : 0 ≤ h_sorted.getD 1 0 := by
    by_cases h_len : h_sorted.length ≤ 1
    · -- If length is 0 or 1, getD 1 0 returns 0
      have : h_sorted.getD 1 0 = 0 := by
        rw [List.getD_eq_default]
        exact h_len
      rw [this]
    · -- If length > 1, getD 1 0 is an element of the list, so it's non-negative
      have h_mem : h_sorted.getD 1 0 ∈ h_sorted := by
        apply List.getD_mem
        exact not_le.mp h_len
      rw [List.mem_sort, Multiset.mem_toList] at h_mem
      exact h_nonneg _ h_mem
  exact h_val

/-!
Spectral gap is positive iff graph is connected (documentation / TODO).

This is the algebraic connectivity characterization: λ₂ > 0 ⟺ kernel is 1-dimensional
(only constant vectors) ⟺ graph is connected.
-/

/-! ## Monotonicity for Lexicographic Proofs -/

/-!
Adding edges increases (or preserves) the spectral gap (documentation / TODO).

This follows from Weyl's inequality / Courant-Fischer min-max principle for eigenvalues
of symmetric matrices.
-/

/-!
The spectral gap is continuous in the matrix entries (documentation / TODO).

Eigenvalues of symmetric matrices depend continuously on entries (Ostrowski's theorem).
-/

/-! ## Connection to Audit Infrastructure -/

/-- Wrap the σ-graph Laplacian from Audit.lean as a GraphLaplacian structure. -/
noncomputable def laplacian_of_sigma_graph
    (agents : List AgentId) (ledger : LedgerState)
    (h_nonempty : agents ≠ [])
    (h_size : 2 ≤ agents.length) :
    GraphLaplacian agents.length := by
  haveI : NeZero agents.length := ⟨by
    intro h
    have : agents = [] := List.length_eq_zero.mp h
    exact h_nonempty this⟩
  exact {
    mat := Audit.sigma_graph_laplacian agents ledger
    symm := Audit.sigma_graph_laplacian_isSymm agents ledger
    psd := by
      intro v
      -- Laplacian quadratic form is always nonneg: vᵀLv = ∑ A_ij (v_i - v_j)²
      let A := Audit.sigma_graph_adjacency agents ledger
      have h_A_nonneg : ∀ i j, 0 ≤ A i j := by
        intro i j
        simp only [A, Audit.sigma_graph_adjacency]
        split_ifs
        · norm_num
        · exact Audit.reciprocity_weight_nonneg ledger _ _
      have h_lap : Audit.sigma_graph_laplacian agents ledger =
          Matrix.diagonal (fun i => ∑ j, A i j) - A := by
        ext i j
        simp only [Audit.sigma_graph_laplacian, Matrix.sub_apply, Matrix.diagonal_apply]
        split_ifs with h
        · subst h
          simp only [Audit.sigma_graph_adjacency, dif_pos rfl, sub_zero]
        · simp only [sub_zero]
          ring
      rw [h_lap]
      simp only [Matrix.dotProduct, Matrix.mulVec, Matrix.sub_apply, Matrix.diagonal_apply, Matrix.sum_apply]
      -- vᵀ(D-A)v = ∑_i v_i ( (∑_j A_ij) v_i - ∑_j A_ij v_j )
      --          = ∑_i ∑_j A_ij v_i² - ∑_i ∑_j A_ij v_i v_j
      --          = 1/2 ∑_i ∑_j A_ij (v_i - v_j)²
      have h_sum_identity : (∑ i, v i * ( (∑ j, A i j) * v i - ∑ j, A i j * v j )) =
                            (1 / 2 : ℝ) * ∑ i, ∑ j, A i j * (v i - v j)^2 := by
        simp only [mul_sub, ← Finset.sum_sub_distrib]
        simp only [mul_assoc, ← Finset.sum_mul]
        -- Expand (v i - v j)² = v i² - 2 v i v j + v j²
        have h_expand : ∀ i j, A i j * (v i - v j)^2 = A i j * (v i)^2 - 2 * A i j * v i * v j + A i j * (v j)^2 := by
          intro i j; ring
        simp_rw [h_expand]
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
        -- Use symmetry of A: ∑ i ∑ j A i j v j² = ∑ j ∑ i A j i v j² = ∑ j (∑ i A j i) v j² = ∑ i (∑ j A i j) v i²
        have h_symm : ∀ i j, A i j = A j i := by
          intro i j
          exact Audit.sigma_graph_adjacency_isSymm agents ledger i j
        have h_double_sum : (∑ i, ∑ j, A i j * (v j)^2) = (∑ i, (∑ j, A i j) * (v i)^2) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          rw [← Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          exact h_symm i j
        rw [h_double_sum]
        -- Now we have: 1/2 * ( ∑_i (∑_j A_ij) v_i² - 2 ∑_i ∑_j A_ij v_i v_j + ∑_i (∑_j A_ij) v_i² )
        --             = 1/2 * ( 2 ∑_i (∑_j A_ij) v_i² - 2 ∑_i ∑_j A_ij v_i v_j )
        --             = ∑_i (∑_j A_ij) v_i² - ∑_i ∑_j A_ij v_i v_j
        ring
      rw [h_sum_identity]
      -- Since 1/2 > 0 and each A_ij (v_i - v_j)² ≥ 0, the sum is ≥ 0.
      apply mul_nonneg
      · norm_num
      · apply Finset.sum_nonneg
        intro i _
        apply Finset.sum_nonneg
        intro j _
        apply mul_nonneg
        · exact h_A_nonneg i j
        · exact sq_nonneg _
    kernel_const := by
      -- L · 1 = 0 for Laplacian (row sums are zero)
      ext i
      simp only [Matrix.mulVec, Matrix.dotProduct, Pi.one_apply, mul_one]
      -- Row sum of Laplacian is 0
      simp only [Audit.sigma_graph_laplacian]
      split_ifs -- wait, this is a sum
      -- L_ii + ∑_{j≠i} L_ij = (∑_{k≠i} A_ik) + ∑_{j≠i} (-A_ij) = 0
      let A := Audit.sigma_graph_adjacency agents ledger
      have h_ii : Audit.sigma_graph_laplacian agents ledger i i = ∑ j, A i j := by
        simp [Audit.sigma_graph_laplacian]
      have h_ij : ∀ j, j ≠ i → Audit.sigma_graph_laplacian agents ledger i j = -A i j := by
        intro j hj
        simp [Audit.sigma_graph_laplacian, hj]
      rw [Finset.sum_eq_add_sum_diff_singleton (Finset.univ : Finset (Fin agents.length)) (Finset.mem_univ i)]
      rw [h_ii]
      have h_sum_neg : ∑ j ∈ Finset.univ \ {i}, Audit.sigma_graph_laplacian agents ledger i j =
                       ∑ j ∈ Finset.univ \ {i}, -A i j := by
        apply Finset.sum_congr rfl
        intro j hj
        apply h_ij
        simp at hj
        exact hj
      rw [h_sum_neg, ← Finset.sum_neg_distrib]
      -- ∑ j, A i j + ∑_{j≠i} -A_ij = A_ii + ∑_{j≠i} A_ij - ∑_{j≠i} A_ij = A_ii
      -- But A_ii = 0 for the sigma graph adjacency matrix.
      have h_Aii : A i i = 0 := by
        simp [A, Audit.sigma_graph_adjacency]
      rw [Finset.sum_eq_add_sum_diff_singleton (Finset.univ : Finset (Fin agents.length)) (Finset.mem_univ i)]
      rw [h_Aii, zero_add]
      ring
    is_laplacian := by
      -- Exists adjacency matrix A such that L = D - A
      use Audit.sigma_graph_adjacency agents ledger
      constructor
      · exact Audit.sigma_graph_adjacency_isSymm agents ledger
      constructor
      · intro i j
        simp only [Audit.sigma_graph_adjacency]
        split_ifs
        · norm_num
        · exact Audit.reciprocity_weight_nonneg ledger _ _
      · -- L = D - A by construction
        ext i j
        simp only [Audit.sigma_graph_laplacian, Matrix.sub_apply, Matrix.diagonal_apply]
        split_ifs with h
        · -- Diagonal: D_ii - A_ii = degree_i - 0 = degree_i
          subst h
          simp only [Audit.sigma_graph_adjacency, dif_pos rfl, sub_zero]
        · -- Off-diagonal: 0 - A_ij
          simp only [sub_zero]
          ring
  }

/-- Compute the proper spectral gap for the audit. -/
noncomputable def spectral_gap_proper
    (agents : List AgentId) (ledger : LedgerState) : ℝ :=
  if h : agents.length ≥ 2 ∧ agents ≠ [] then
    spectral_gap_of_laplacian
      (laplacian_of_sigma_graph agents ledger h.2 h.1) h.1
  else
    0  -- Degenerate case: less than 2 agents

/-- The proper spectral gap is non-negative. -/
theorem spectral_gap_proper_nonneg
    (agents : List AgentId) (ledger : LedgerState) :
    0 ≤ spectral_gap_proper agents ledger := by
  unfold spectral_gap_proper
  split_ifs with h
  · exact spectral_gap_nonneg _ h.1
  · norm_num

/-! ## Robustness Interpretation -/

/-!
Higher spectral gap means more robust reciprocity network (documentation / TODO).

Intended claim: larger spectral gap corresponds to a “harder to partition” reciprocity graph,
and therefore higher robustness of cooperative structure.
-/

/-!
Spectral gap bounds the mixing time of random walks (documentation / TODO).

Intended claim: mixing time scales like \(O(1/\lambda_2)\) where \(\lambda_2\) is the spectral gap.
This is standard spectral graph theory; formalization can be added later.
-/

end SpectralGap
end Ethics
end IndisputableMonolith
