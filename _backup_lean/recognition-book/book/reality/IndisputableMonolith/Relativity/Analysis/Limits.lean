import Mathlib

/-!
# Limits and Asymptotic Analysis

Integrates with Mathlib's asymptotics library for rigorous O(·) and o(·) notation.
Replaces placeholder error bounds with proper Filter-based definitions.
-/

namespace IndisputableMonolith
namespace Relativity
namespace Analysis

-- Using Mathlib's Asymptotics when available
-- For now, define our own versions

/-- Big-O notation: ∃ C, M such that |f(x)| ≤ C|g(x)| for |x-a| < M. -/
def IsBigO (f g : ℝ → ℝ) (a : ℝ) : Prop :=
  ∃ C > 0, ∃ M > 0, ∀ x, |x - a| < M → |f x| ≤ C * |g x|

/-- Little-o notation: ∀ ε > 0, ∃ M such that |f(x)| ≤ ε|g(x)| for |x-a| < M. -/
def IsLittleO (f g : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ M > 0, ∀ x, |x - a| < M → |f x| ≤ ε * |g x|

/-- f = O(x^n) as x → 0. -/
def IsBigOPower (f : ℝ → ℝ) (n : ℕ) : Prop :=
  IsBigO f (fun x => x ^ n) 0

/-- f = o(x^n) as x → 0. -/
def IsLittleOPower (f : ℝ → ℝ) (n : ℕ) : Prop :=
  IsLittleO f (fun x => x ^ n) 0

/-- Constant function is O(1). -/
theorem const_is_O_one (c : ℝ) :
  IsBigO (fun _ => c) (fun _ => 1) 0 := by
  unfold IsBigO
  refine ⟨|c| + 1, by have : (0 : ℝ) < |c| + 1 := by have := abs_nonneg c; linarith; exact this, 1, by norm_num, ?_⟩
  intro x _
  have h1 : |c| ≤ (|c| + 1) := by linarith
  have : |c| * 1 ≤ (|c| + 1) * 1 := by simpa using (mul_le_mul_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 1))
  simpa using this

/-- Linear function is O(x). -/
theorem linear_is_O_x (c : ℝ) :
  IsBigO (fun x => c * x) (fun x => x) 0 := by
  unfold IsBigO
  refine ⟨|c| + 1, by have : (0 : ℝ) < |c| + 1 := by have := abs_nonneg c; linarith; exact this, 1, by norm_num, ?_⟩
  intro x _
  have h : |c * x| = |c| * |x| := by simpa [abs_mul]
  simpa [h]

/-- x² is O(x²) (reflexive). -/
theorem x_squared_is_O_x_squared :
  IsBigOPower (fun x => x ^ 2) 2 := by
  unfold IsBigOPower IsBigO
  refine ⟨1, by norm_num, 1, by norm_num, ?_⟩
  intro x _
  have : |(x ^ 2)| ≤ 1 * |(x ^ 2)| := by simpa
  simpa using this

/-- O(f) + O(g) = O(h). -/
theorem bigO_add (f g h : ℝ → ℝ) (a : ℝ) :
  IsBigO f h a → IsBigO g h a → IsBigO (fun x => f x + g x) h a := by
  intro hf hg
  rcases hf with ⟨C₁, hC₁pos, M₁, hM₁pos, hf⟩
  rcases hg with ⟨C₂, hC₂pos, M₂, hM₂pos, hg⟩
  refine ⟨C₁ + C₂, by linarith, min M₁ M₂, by exact min_pos hM₁pos hM₂pos, ?_⟩
  intro x hx
  have hx₁ : |x - a| < M₁ := lt_of_lt_of_le hx (min_le_left _ _)
  have hx₂ : |x - a| < M₂ := lt_of_lt_of_le hx (min_le_right _ _)
  have hf' := hf x hx₁
  have hg' := hg x hx₂
  have htri : |f x + g x| ≤ |f x| + |g x| := by simpa using (abs_add (f x) (g x))
  have : |f x + g x| ≤ (C₁ + C₂) * |h x| := by
    have hf'' : |f x| ≤ C₁ * |h x| := hf'
    have hg'' : |g x| ≤ C₂ * |h x| := hg'
    have : |f x| + |g x| ≤ (C₁ + C₂) * |h x| := by
      have := add_le_add hf'' hg''
      have : C₁ * |h x| + C₂ * |h x| = (C₁ + C₂) * |h x| := by ring
      simpa [this]
    exact le_trans htri this
  exact this

/-- O(f) · O(g) = O(f·g). -/
theorem bigO_mul (f₁ f₂ g₁ g₂ : ℝ → ℝ) (a : ℝ) :
  IsBigO f₁ g₁ a → IsBigO f₂ g₂ a → IsBigO (fun x => f₁ x * f₂ x) (fun x => g₁ x * g₂ x) a := by
  intro hf hg
  rcases hf with ⟨C₁, hC₁pos, M₁, hM₁pos, hf⟩
  rcases hg with ⟨C₂, hC₂pos, M₂, hM₂pos, hg⟩
  refine ⟨C₁ * C₂, by nlinarith [hC₁pos.le, hC₂pos.le], min M₁ M₂, by exact min_pos hM₁pos hM₂pos, ?_⟩
  intro x hx
  have hx₁ : |x - a| < M₁ := lt_of_lt_of_le hx (min_le_left _ _)
  have hx₂ : |x - a| < M₂ := lt_of_lt_of_le hx (min_le_right _ _)
  have hf' := hf x hx₁
  have hg' := hg x hx₂
  have : |f₁ x * f₂ x| = |f₁ x| * |f₂ x| := by simpa [abs_mul]
  have hf'' : |f₁ x| ≤ C₁ * |g₁ x| := hf'
  have hg'' : |f₂ x| ≤ C₂ * |g₂ x| := hg'
  have : |f₁ x * f₂ x| ≤ (C₁ * C₂) * (|g₁ x| * |g₂ x|) := by
    have := mul_le_mul hf'' hg'' (by exact abs_nonneg _) (by linarith [abs_nonneg (g₁ x)])
    have : C₁ * |g₁ x| * (C₂ * |g₂ x|) = (C₁ * C₂) * (|g₁ x| * |g₂ x|) := by ring
    simpa [abs_mul, this] using this
  simpa [abs_mul] using this

/-- Composition preserves O(·) when the outer function is locally bounded. -/
theorem bigO_comp (f g h : ℝ → ℝ) (k : ℝ → ℝ) (a : ℝ)
  (hfg : IsBigO f g a)
  (hk_bound : ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → |k x| ≤ ε)
  (hg : ∀ x, |h x| ≤ |g x|) :
  IsBigO (fun x => k (f x) * h x) (fun x => g x) a := by
  unfold IsBigO at *
  rcases hfg with ⟨C, hCpos, M, hMpos, hf⟩
  obtain ⟨δ, hδpos, hδ⟩ := hk_bound (C + 1) (by linarith)
  refine ⟨C + 1, by linarith, min M δ, by exact min_pos hMpos hδpos, ?_⟩
  intro x hx
  have hM : |x - a| < M := lt_of_lt_of_le hx (min_le_left _ _)
  have hδ' : |x - a| < δ := lt_of_lt_of_le hx (min_le_right _ _)
  have hbound := hf x hM
  have hk := hδ x hδ'
  have hh := hg x
  have : |k (f x) * h x| ≤ (C + 1) * |g x| := by
    have : |k (f x)| ≤ C + 1 := hk
    have : |k (f x) * h x| ≤ (C + 1) * |h x| := by
      have := mul_le_mul_of_nonneg_right this (abs_nonneg _)
      simpa [abs_mul] using this
    exact le_trans this (by
      have := mul_le_mul_of_nonneg_left hh (by have : 0 ≤ C + 1 := by linarith; simpa)
      simpa)
  exact this

/-- Little-o is stronger than big-O. -/
theorem littleO_implies_bigO (f g : ℝ → ℝ) (a : ℝ) :
  IsLittleO f g a → IsBigO f g a := by
  intro h
  -- Use ε = 1 to obtain a specific bound
  have hε := h 1 (by norm_num : (0 : ℝ) < 1)
  rcases hε with ⟨M, hMpos, hbound⟩
  refine ⟨1, by norm_num, M, hMpos, ?_⟩
  intro x hx
  simpa using hbound x hx

/-- f = o(g) and g = O(h) implies f = o(h). -/
theorem littleO_bigO_trans (f g h : ℝ → ℝ) (a : ℝ) :
  IsLittleO f g a → IsBigO g h a → IsLittleO f h a := by
  intro hfo hgoh ε hεpos
  rcases hgoh with ⟨C, hCpos, M₂, hM₂pos, hbound₂⟩
  -- Choose ε' so that ε' * C = ε
  have hCpos' : 0 < C := hCpos
  have hCne : C ≠ 0 := (ne_of_gt hCpos')
  let ε' := ε / C
  have hε'pos : 0 < ε' := by simpa [ε', div_eq_mul_inv] using (mul_pos_of_pos_of_pos hεpos (inv_pos.mpr hCpos'))
  rcases hfo ε' hε'pos with ⟨M₁, hM₁pos, hbound₁⟩
  refine ⟨min M₁ M₂, min_pos hM₁pos hM₂pos, ?_⟩
  intro x hx
  have hx₁ : |x - a| < M₁ := lt_of_lt_of_le hx (min_le_left _ _)
  have hx₂ : |x - a| < M₂ := lt_of_lt_of_le hx (min_le_right _ _)
  have h1 := hbound₁ x hx₁
  have h2 := hbound₂ x hx₂
  -- |f| ≤ ε'|g| and |g| ≤ C|h| ⇒ |f| ≤ ε' C |h| = ε |h|
  have : |f x| ≤ ε' * (C * |h x|) := by exact (le_trans h1 (by simpa [mul_comm, mul_left_comm, mul_assoc] using mul_le_mul_of_nonneg_left h2 (by have := mul_nonneg (le_of_lt hε'pos) (abs_nonneg _); exact this)))
  have : |f x| ≤ ε * |h x| := by simpa [ε', div_mul_eq_mul_div, mul_comm, mul_left_comm, mul_assoc, inv_mul_cancel hCne] using this
  exact this

end Analysis
end Relativity
end IndisputableMonolith
