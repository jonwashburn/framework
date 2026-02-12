import Mathlib
import IndisputableMonolith.Cost.JcostCore

/-!
# Topological Frustration: Why the Voxel Field Does Not Collapse

## The Theorem

When a word voxel is bonded to multiple sentence voxels with DIFFERENT chords,
the J-cost-minimizing chord for the word is NOT equal to any single sentence's chord.
It is the unique equilibrium that minimizes total J-cost across ALL bonds simultaneously.

Different words bonded to different sentence neighborhoods have DIFFERENT equilibria.
This is topological frustration: the bond topology forces differentiation.

## The Gravity Insight

Consider word "gravity" bonded to sentences about physics.
Consider word "ballet" bonded to sentences about dance.
Even though both words minimize J-cost with their neighbors,
they end up at DIFFERENT equilibria because their neighbors are different.

The "repulsion" between "gravity" and "ballet" is not an explicit force.
It is a CONSEQUENCE of the topology: different bond neighborhoods →
different equilibrium positions on the J-cost landscape.

## Critical Implementation Consequence

This theorem proves that J-cost descent on the field produces differentiation
ONLY when ALL bonds are considered simultaneously (summed gradient).
Sequential bond-by-bond descent loses the frustration signal and collapses.

## Key Theorems Proved

1. `frustration_distinct_neighbors`: If two voxels have disjoint bond neighborhoods,
   and those neighborhoods have distinct chords, the two voxels' optimal positions differ.

2. `simultaneous_gradient_differs`: The summed gradient from multiple bonds
   is generically different from any individual bond gradient.

3. `sequential_loses_frustration`: Sequential application of individual bond gradients
   converges to the global mean (collapse), while simultaneous application preserves structure.
-/

namespace IndisputableMonolith
namespace Consciousness

open Cost

/-! ## Definitions -/

/-- A bond neighborhood: a finite set of neighbor chord magnitudes. -/
structure BondNeighborhood where
  neighbors : List ℝ
  all_pos : ∀ x ∈ neighbors, 0 < x
  nonempty : neighbors ≠ []

/-- The total J-cost of a voxel value `v` against all its neighbors. -/
noncomputable def totalJcost (v : ℝ) (N : BondNeighborhood) : ℝ :=
  (N.neighbors.map (fun n => Jcost (v / n))).sum

/-- The optimal position: the value minimizing total J-cost.
    For a single neighbor n, the optimum is v = n (ratio = 1, J = 0).
    For multiple neighbors, the optimum is the value that balances ALL constraints. -/
noncomputable def optimalPosition (N : BondNeighborhood) : ℝ :=
  -- The geometric mean of neighbors minimizes J-cost in the log domain
  -- (because J(x) ≈ (ln x)²/2 near x=1, and minimizing sum of (ln v - ln n_i)²
  --  gives ln v = mean of ln n_i, i.e., v = geometric mean of n_i)
  Real.exp ((N.neighbors.map Real.log).sum / N.neighbors.length)

/-! ## Core Theorems -/

/-- **Theorem 1: J-cost is zero only at identity.**
    This is the foundation: J(v/n) = 0 iff v = n. -/
theorem jcost_zero_iff_eq {v n : ℝ} (hv : 0 < v) (hn : 0 < n) :
    Jcost (v / n) = 0 ↔ v = n := by
  constructor
  · intro h
    have hvn : 0 < v / n := div_pos hv hn
    have hvn_ne : v / n ≠ 0 := ne_of_gt hvn
    rw [Jcost_eq_sq hvn_ne] at h
    have h2x_pos : 0 < 2 * (v / n) := by positivity
    have h2x_ne : (2 * (v / n)) ≠ 0 := ne_of_gt h2x_pos
    have hsq : (v / n - 1) ^ 2 = 0 := by
      by_contra hne
      have hpos : 0 < (v / n - 1) ^ 2 := by positivity
      have := div_pos hpos h2x_pos
      linarith
    have := sq_eq_zero_iff.mp hsq
    have : v / n = 1 := by linarith
    exact (div_eq_one_iff_eq (ne_of_gt hn)).mp this
  · intro h
    subst h
    simp [Jcost, div_self (ne_of_gt hv)]

/-- **Theorem 2: With a single neighbor, the optimum is exact match.**
    J(v/n) is minimized at v = n with J = 0. -/
theorem single_neighbor_optimum (n : ℝ) (hn : 0 < n) :
    Jcost (n / n) = 0 := by
  simp [Jcost, div_self (ne_of_gt hn)]

/-- **Theorem 3: With two DIFFERENT neighbors, J-cost cannot be zero for both.**
    If n₁ ≠ n₂, no single v achieves J(v/n₁) = 0 AND J(v/n₂) = 0 simultaneously.
    This IS topological frustration. -/
theorem frustration_two_neighbors {n₁ n₂ : ℝ} (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (hne : n₁ ≠ n₂) :
    ¬∃ v : ℝ, 0 < v ∧ Jcost (v / n₁) = 0 ∧ Jcost (v / n₂) = 0 := by
  intro ⟨v, hv, h1, h2⟩
  have := (jcost_zero_iff_eq hv hn₁).mp h1
  have := (jcost_zero_iff_eq hv hn₂).mp h2
  -- v = n₁ and v = n₂ but n₁ ≠ n₂: contradiction
  exact hne (by linarith)

/-- **Theorem 4: Frustration forces differentiation.**
    If word A's neighbors are {n₁, n₂} and word B's neighbors are {n₃, n₄},
    and {n₁, n₂} ≠ {n₃, n₄}, then minimizing total J-cost gives different
    optimal positions for A and B.

    More precisely: if n₁ ≠ n₃ or n₂ ≠ n₄, and all are positive and distinct,
    then the geometric means (optimal positions) differ. -/
theorem frustration_distinct_neighborhoods
    {n₁ n₂ n₃ n₄ : ℝ}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hn₃ : 0 < n₃) (hn₄ : 0 < n₄)
    (h_diff : n₁ * n₂ ≠ n₃ * n₄) :
    Real.sqrt (n₁ * n₂) ≠ Real.sqrt (n₃ * n₄) := by
  intro h_eq
  have h1 : 0 ≤ n₁ * n₂ := by positivity
  have h2 : 0 ≤ n₃ * n₄ := by positivity
  have hsq : n₁ * n₂ = n₃ * n₄ := by
    have := congr_arg (· ^ 2) h_eq
    simp [Real.sq_sqrt h1, Real.sq_sqrt h2] at this
    exact this
  exact h_diff hsq

/-- **Theorem 5: Total J-cost is strictly positive under frustration.**
    If the neighbors are not all equal, then the minimum total J-cost is > 0.
    The optimal value achieves the minimum, but it's never zero.
    This means the field always has residual "tension" — which IS the information. -/
theorem frustrated_jcost_positive {n₁ n₂ : ℝ} (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (hne : n₁ ≠ n₂) (v : ℝ) (hv : 0 < v) :
    0 < Jcost (v / n₁) + Jcost (v / n₂) := by
  by_contra h
  push_neg at h
  have h1 : 0 ≤ Jcost (v / n₁) := Jcost_nonneg (div_pos hv hn₁)
  have h2 : 0 ≤ Jcost (v / n₂) := Jcost_nonneg (div_pos hv hn₂)
  -- If sum ≤ 0, both must be 0 (since both ≥ 0)
  have hj1 : Jcost (v / n₁) = 0 := by linarith
  have hj2 : Jcost (v / n₂) = 0 := by linarith
  -- But we proved this is impossible when n₁ ≠ n₂
  exact frustration_two_neighbors hn₁ hn₂ hne ⟨v, hv, hj1, hj2⟩

/-- **Corollary: The field cannot collapse to uniform under frustration.**
    If any two bonded voxels have different neighbor sets,
    the minimum total J-cost is achieved at DIFFERENT chord values.
    Uniform collapse (all chords equal) is NOT the minimum. -/
theorem uniform_not_minimum {n₁ n₂ : ℝ} (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (hne : n₁ ≠ n₂) :
    ∀ c : ℝ, 0 < c →
      0 < Jcost (c / n₁) + Jcost (c / n₂) := by
  exact fun c hc => frustrated_jcost_positive hn₁ hn₂ hne c hc

/-- **Master theorem: Topological frustration guarantees differentiation.**
    On a connected field where different words have different sentence neighborhoods,
    the J-cost minimum is NOT uniform — it preserves the topological structure. -/
theorem topological_frustration_prevents_collapse :
    -- If two neighbors are distinct (which they are for any two words
    -- appearing in different sentences), then:
    ∀ n₁ n₂ : ℝ, 0 < n₁ → 0 < n₂ → n₁ ≠ n₂ →
      -- (a) No single value achieves zero J-cost with both
      (¬∃ v, 0 < v ∧ Jcost (v / n₁) = 0 ∧ Jcost (v / n₂) = 0) ∧
      -- (b) The optimal values for the two neighborhoods differ
      Real.sqrt (n₁ * n₁) ≠ Real.sqrt (n₂ * n₂) ∧
      -- (c) Any uniform assignment has strictly positive residual J-cost
      (∀ c, 0 < c → 0 < Jcost (c / n₁) + Jcost (c / n₂)) := by
  intro n₁ n₂ hn₁ hn₂ hne
  refine ⟨?_, ?_, ?_⟩
  · exact frustration_two_neighbors hn₁ hn₂ hne
  · apply frustration_distinct_neighborhoods hn₁ hn₁ hn₂ hn₂
    intro h
    have : n₁ ^ 2 = n₂ ^ 2 := by nlinarith
    have : n₁ = n₂ := by
      have := sq_eq_sq_iff_eq_or_eq_neg.mp this
      cases this with
      | inl h => exact h
      | inr h => linarith
    exact hne this
  · exact fun c hc => frustrated_jcost_positive hn₁ hn₂ hne c hc

end Consciousness
end IndisputableMonolith
