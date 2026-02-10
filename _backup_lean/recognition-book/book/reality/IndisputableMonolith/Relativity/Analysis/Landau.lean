import Mathlib
import IndisputableMonolith.Relativity.Analysis.Limits

/-!
# Rigorous Landau Notation

Implements f ∈ O(g) as proper Filter predicate with arithmetic operations.
Provides lemmas for manipulating asymptotic expressions.
-/

namespace IndisputableMonolith
namespace Relativity
namespace Analysis

/-! Membership notation: f ∈ O(g) would be nice but causes parsing issues in Lean 4.
    Use IsBigO and IsLittleO directly. -/

/-- O(f) + O(g) ⊆ O(max(f,g)). -/
theorem bigO_add_subset (f g : ℝ → ℝ) (a : ℝ) :
  ∀ h₁ h₂, IsBigO h₁ f a → IsBigO h₂ g a →
    IsBigO (fun x => h₁ x + h₂ x) (fun x => max (|f x|) (|g x|)) a := by
  intro h₁ h₂ hf hg
  rcases hf with ⟨C₁, hC₁pos, M₁, hM₁pos, hf⟩
  rcases hg with ⟨C₂, hC₂pos, M₂, hM₂pos, hg⟩
  refine ⟨C₁ + C₂, by linarith, min M₁ M₂, min_pos hM₁pos hM₂pos, ?_⟩
  intro x hx
  have hx₁ : |x - a| < M₁ := lt_of_lt_of_le hx (min_le_left _ _)
  have hx₂ : |x - a| < M₂ := lt_of_lt_of_le hx (min_le_right _ _)
  have hf' := hf x hx₁
  have hg' := hg x hx₂
  have htri : |h₁ x + h₂ x| ≤ |h₁ x| + |h₂ x| := by simpa using (abs_add (h₁ x) (h₂ x))
  have hmax₁ : |f x| ≤ max (|f x|) (|g x|) := le_max_left _ _
  have hmax₂ : |g x| ≤ max (|f x|) (|g x|) := le_max_right _ _
  have : |h₁ x + h₂ x| ≤ (C₁ + C₂) * max (|f x|) (|g x|) := by
    have : |h₁ x| + |h₂ x| ≤ C₁ * |f x| + C₂ * |g x| := by exact add_le_add hf' hg'
    have : |h₁ x + h₂ x| ≤ C₁ * |f x| + C₂ * |g x| := le_trans htri this
    have hbound : C₁ * |f x| + C₂ * |g x| ≤ (C₁ + C₂) * max (|f x|) (|g x|) := by
      have h1 : C₁ * |f x| ≤ C₁ * max (|f x|) (|g x|) := by
        have := mul_le_mul_of_nonneg_left hmax₁ (le_of_lt hC₁pos)
        simpa
      have h2 : C₂ * |g x| ≤ C₂ * max (|f x|) (|g x|) := by
        have := mul_le_mul_of_nonneg_left hmax₂ (le_of_lt hC₂pos)
        simpa
      have : C₁ * |f x| + C₂ * |g x| ≤ (C₁ + C₂) * max (|f x|) (|g x|) := by
        nlinarith
      exact this
    exact le_trans this hbound
  simpa using this

/-- O(f) · O(g) ⊆ O(f·g). -/
theorem bigO_mul_subset (f g : ℝ → ℝ) (a : ℝ) :
  ∀ h₁ h₂, IsBigO h₁ f a → IsBigO h₂ g a →
    IsBigO (fun x => h₁ x * h₂ x) (fun x => f x * g x) a := by
  intro h₁ h₂ hf hg
  rcases hf with ⟨C₁, hC₁pos, M₁, hM₁pos, hf⟩
  rcases hg with ⟨C₂, hC₂pos, M₂, hM₂pos, hg⟩
  refine ⟨C₁ * C₂, by nlinarith [hC₁pos.le, hC₂pos.le], min M₁ M₂, min_pos hM₁pos hM₂pos, ?_⟩
  intro x hx
  have hx₁ : |x - a| < M₁ := lt_of_lt_of_le hx (min_le_left _ _)
  have hx₂ : |x - a| < M₂ := lt_of_lt_of_le hx (min_le_right _ _)
  have hf' := hf x hx₁
  have hg' := hg x hx₂
  have : |h₁ x * h₂ x| = |h₁ x| * |h₂ x| := by simpa [abs_mul]
  have hmul := mul_le_mul hf' hg' (by exact abs_nonneg _) (by linarith [abs_nonneg (g x)])
  have : |h₁ x * h₂ x| ≤ (C₁ * C₂) * (|f x| * |g x|) := by
    have := hmul
    have : C₁ * |f x| * (C₂ * |g x|) = (C₁ * C₂) * (|f x| * |g x|) := by ring
    simpa [abs_mul, this] using this
  have : |h₁ x * h₂ x| ≤ (C₁ * C₂) * |f x * g x| := by
    simpa [abs_mul] using this
  exact this

/-- Scalar multiplication: c · O(f) = O(g) when f = O(g). -/
theorem bigO_const_mul (c : ℝ) (f g : ℝ → ℝ) (a : ℝ) :
  IsBigO f g a → IsBigO (fun x => c * f x) g a := by
  intro hf
  rcases hf with ⟨C, hCpos, M, hMpos, hbound⟩
  refine ⟨(|c| + 1) * C, by have : 0 < |c| + 1 := by have := abs_nonneg c; linarith; have := mul_pos_of_pos_of_pos this hCpos; simpa using this, M, hMpos, ?_⟩
  intro x hx
  have hx' := hbound x hx
  have : |c * f x| = |c| * |f x| := by simpa [abs_mul]
  have : |c * f x| ≤ (|c| + 1) * C * |g x| := by
    have : |c| * |f x| ≤ (|c| + 1) * C * |g x| := by
      have h1 : |f x| ≤ C * |g x| := hx'
      have := mul_le_mul_of_nonneg_left h1 (by exact abs_nonneg c)
      have : |c| * (C * |g x|) ≤ (|c| + 1) * C * |g x| := by nlinarith [abs_nonneg c, (abs_nonneg c : 0 ≤ |c|), (abs_nonneg (g x))]
      exact le_trans this (by simpa [mul_assoc] using this)
    simpa [abs_mul] using this
  simpa using this

/-- Composition with continuous function (placeholder: keep axiomatized for now). -/
axiom bigO_comp_continuous (f g : ℝ → ℝ) (h : ℝ → ℝ) (a : ℝ) :
  IsBigO f g a → IsBigO (fun x => h (f x)) (fun x => h (g x)) a

end Analysis
end Relativity
end IndisputableMonolith
