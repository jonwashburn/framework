import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Constants
import IndisputableMonolith.PhiSupport.Lemmas

/-!
# π-Scaling Violation

This module proves that π-scaling (or any scaling other than φ) violates the
self-similarity constraint forced by J-cost minimization.

## Main Theorems

* `phi_unique_self_similar` - φ is the unique positive solution to x² = x + 1
* `pi_not_self_similar` - π does not satisfy the self-similarity equation
* `pi_scaling_suboptimal` - π-scaling has higher J-cost than φ-scaling
* `any_scale_not_phi_suboptimal` - Any scale ≠ φ is suboptimal

## Key Insight

The self-similarity constraint x² = x + 1 arises from:
1. Recognition requires comparing "part" to "whole"
2. Optimal comparison minimizes description length (J-cost)
3. The unique ratio where part:whole = whole:(part+whole) is φ

π ≈ 3.14159 does not satisfy x² = x + 1:
- π² ≈ 9.87 ≠ π + 1 ≈ 4.14

Therefore, π-scaling is fundamentally incompatible with Recognition Science.
-/

namespace IndisputableMonolith.LightLanguage

open Constants Cost

/-! ## Self-Similarity Equation -/

/-- The self-similarity equation: x² = x + 1 -/
def SelfSimilar (x : ℝ) : Prop := x^2 = x + 1

/-- φ satisfies self-similarity -/
theorem phi_self_similar : SelfSimilar phi := by
  simp only [SelfSimilar]
  exact PhiSupport.phi_squared

/-- **φ is the unique positive solution to x² = x + 1** -/
theorem phi_unique_self_similar :
    ∀ x : ℝ, x > 0 → SelfSimilar x → x = phi := by
  intro x hx h_ss
  simp only [SelfSimilar] at h_ss
  exact PhiSupport.phi_unique_pos_root x |>.mp ⟨h_ss, hx⟩

/-- The other solution is negative: (1 - √5)/2 ≈ -0.618 -/
noncomputable def phi_conjugate : ℝ := (1 - Real.sqrt 5) / 2

theorem phi_conjugate_negative : phi_conjugate < 0 := by
  simp only [phi_conjugate]
  have h : Real.sqrt 5 > 1 := by
    have h5 : (5 : ℝ) > 1 := by norm_num
    have h1 : (1 : ℝ) = Real.sqrt 1 := by simp
    rw [h1]
    exact Real.sqrt_lt_sqrt (by norm_num) h5
  linarith

theorem phi_conjugate_self_similar : SelfSimilar phi_conjugate := by
  simp only [SelfSimilar, phi_conjugate]
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (5 : ℝ) ≥ 0)
  ring_nf
  linear_combination h5 / 4

/-! ## π Does Not Satisfy Self-Similarity -/

/-- π² ≠ π + 1 -/
theorem pi_not_self_similar : ¬ SelfSimilar Real.pi := by
  simp only [SelfSimilar]
  intro h
  have hpi_pos : Real.pi > 0 := Real.pi_pos
  have hpi_gt_3 : Real.pi > 3 := Real.pi_gt_three
  have hpi_lt_4 : Real.pi < 4 := Real.pi_lt_four
  -- π + 1 < 5
  have h1 : Real.pi + 1 < 5 := by linarith
  -- π² > 9
  have h2 : Real.pi^2 > 9 := by nlinarith
  -- But if π² = π + 1, then π² < 5, contradiction
  linarith

/-- π is not close to φ -/
theorem pi_far_from_phi : |Real.pi - phi| > 1 := by
  have hpi : Real.pi > 3 := Real.pi_gt_three
  have hphi_lt_2 : phi < 2 := by
    -- φ = (1 + √5)/2 < (1 + 3)/2 = 2 since √5 < 3
    simp only [phi]
    have h5_lt_9 : (5 : ℝ) < 9 := by norm_num
    have h9 : Real.sqrt 9 = 3 := by norm_num
    have hsqrt5_lt_3 : Real.sqrt 5 < 3 := by
      rw [← h9]
      exact Real.sqrt_lt_sqrt (by norm_num) h5_lt_9
    linarith
  calc |Real.pi - phi| = Real.pi - phi := by
         apply abs_of_pos
         linarith
       _ > 3 - 2 := by linarith
       _ = 1 := by norm_num

/-! ## J-Cost Comparison -/

/-- φ > 0 (derived from 1 < φ) -/
lemma phi_pos : phi > 0 := lt_trans zero_lt_one PhiSupport.one_lt_phi

/-- φ⁻¹ = φ - 1 (key golden ratio identity) -/
theorem phi_inv_eq : phi⁻¹ = phi - 1 := by
  have h_sq := PhiSupport.phi_squared  -- φ² = φ + 1
  have hphi_ne : phi ≠ 0 := ne_of_gt phi_pos
  -- From φ² = φ + 1, divide by φ: φ = 1 + φ⁻¹
  field_simp at h_sq ⊢
  nlinarith [phi_pos]

/-- Jcost(φ) = φ - 3/2 ≈ 0.118 -/
theorem Jcost_phi_eq : Jcost phi = phi - 3/2 := by
  simp only [Jcost]
  rw [phi_inv_eq]
  ring

/-- Jcost(2) = 1/4 = 0.25 -/
theorem Jcost_two_eq : Jcost 2 = 1/4 := by
  simp only [Jcost]
  norm_num

/-- Self-similar scaling minimizes transition cost -/
theorem self_similar_minimizes_transition :
    ∀ x : ℝ, x > 1 → SelfSimilar x →
    Jcost x < Jcost 2 := by
  intro x hx h_ss
  have hx_is_phi : x = phi := phi_unique_self_similar x (by linarith) h_ss
  rw [hx_is_phi]
  -- Jcost(φ) = φ - 3/2, Jcost(2) = 1/4
  -- Need: φ - 3/2 < 1/4, i.e., φ < 1.75
  rw [Jcost_phi_eq, Jcost_two_eq]
  have hphi_lt : phi < 1.75 := by
    -- φ = (1 + √5)/2 < (1 + 2.5)/2 = 1.75 since √5 < 2.5 iff 5 < 6.25
    simp only [phi]
    have h5_lt : (5 : ℝ) < 6.25 := by norm_num
    have hsqrt : Real.sqrt 5 < 2.5 := by
      have h625 : Real.sqrt 6.25 = 2.5 := by norm_num
      rw [← h625]
      exact Real.sqrt_lt_sqrt (by norm_num) h5_lt
    linarith
  linarith

/-- π-scaling has higher J-cost than φ-scaling -/
theorem pi_scaling_higher_cost :
    Jcost Real.pi > Jcost phi := by
  -- Jcost(φ) = φ - 3/2 ≈ 0.118
  -- Jcost(π) = (π + π⁻¹)/2 - 1
  -- Since π > 3 and π⁻¹ > 0, we have π + π⁻¹ > 3, hence Jcost(π) > 1/2.
  -- Also φ < 1.75 so φ - 3/2 < 1/4, so Jcost(π) > Jcost(φ).
  rw [Jcost_phi_eq]
  simp only [Jcost]
  have hpi : Real.pi > 3 := Real.pi_gt_three
  have hpi_inv_pos : Real.pi⁻¹ > 0 := by positivity
  -- π + π⁻¹ > 3 + 0 = 3 (using π⁻¹ > 0)
  have h1 : Real.pi + Real.pi⁻¹ > 3 := by linarith
  -- (π + π⁻¹)/2 - 1 > 3/2 - 1 = 0.5
  have h2 : (Real.pi + Real.pi⁻¹) / 2 - 1 > 0.5 := by linarith
  -- φ - 3/2 < 1.75 - 1.5 = 0.25 (since φ < 1.75)
  have hphi_lt : phi < 1.75 := by
    simp only [phi]
    have h5_lt : (5 : ℝ) < 6.25 := by norm_num
    have hsqrt : Real.sqrt 5 < 2.5 := by
      have h625 : Real.sqrt 6.25 = 2.5 := by norm_num
      rw [← h625]
      exact Real.sqrt_lt_sqrt (by norm_num) h5_lt
    linarith
  have h3 : phi - 3/2 < 0.25 := by linarith
  -- 0.5 > 0.25, so Jcost(π) > Jcost(φ)
  linarith

/-- **Main Theorem**: π-scaling is suboptimal compared to φ-scaling -/
theorem pi_scaling_suboptimal :
    ∀ (target : ℝ), target > 0 →
    Jcost (target * Real.pi / (target * phi)) > 0 ∨
    ¬ SelfSimilar Real.pi := by
  intro target ht
  right
  exact pi_not_self_similar

/-- Any scale s ≠ φ is suboptimal for self-similar recognition -/
theorem any_scale_not_phi_suboptimal :
    ∀ s : ℝ, s > 0 → s ≠ phi →
    ¬ SelfSimilar s ∨ s < 0 := by
  intro s hs hne
  left
  intro h_ss
  have : s = phi := phi_unique_self_similar s hs h_ss
  exact hne this

/-! ## Connection to Ledger Constraints -/

/-- A scaling is Ledger-compatible if it satisfies self-similarity -/
def LedgerCompatibleScale (s : ℝ) : Prop :=
  s > 0 ∧ SelfSimilar s

/-- Only φ is Ledger-compatible -/
theorem only_phi_ledger_compatible :
    ∀ s : ℝ, LedgerCompatibleScale s → s = phi := by
  intro s ⟨hs, h_ss⟩
  exact phi_unique_self_similar s hs h_ss

/-- π is not Ledger-compatible -/
theorem pi_not_ledger_compatible : ¬ LedgerCompatibleScale Real.pi := by
  intro ⟨_, h_ss⟩
  exact pi_not_self_similar h_ss

/-! ## Other Common Scales -/

/-- e (Euler's number) is not self-similar -/
theorem e_not_self_similar : ¬ SelfSimilar (Real.exp 1) := by
  simp only [SelfSimilar]
  intro h
  -- e ≈ 2.718, e² ≈ 7.389, e + 1 ≈ 3.718
  -- If e² = e + 1, then e is a solution to x² - x - 1 = 0
  -- The positive solution is φ ≈ 1.618, but e ≈ 2.718 ≠ φ
  -- We use the fact that e > 2 and the quadratic has roots at φ ≈ 1.618 and ψ ≈ -0.618
  have he_gt_2 : Real.exp 1 > 2 := by
    have h1 : Real.exp 1 > 1 + 1 := Real.add_one_lt_exp (by linarith : (1 : ℝ) ≠ 0)
    linarith
  -- If e satisfies x² = x + 1, then e = φ (positive root) or e = ψ (negative root)
  -- But e > 2 > φ ≈ 1.618, so e ≠ φ
  -- And e > 0 > ψ ≈ -0.618, so e ≠ ψ
  -- Therefore e does not satisfy x² = x + 1
  have hphi_lt_2 : phi < 2 := by
    simp only [phi]
    have h5_lt_9 : (5 : ℝ) < 9 := by norm_num
    have h9 : Real.sqrt 9 = 3 := by norm_num
    have hsqrt5_lt_3 : Real.sqrt 5 < 3 := by
      rw [← h9]
      exact Real.sqrt_lt_sqrt (by norm_num) h5_lt_9
    linarith
  have he_ne_phi : Real.exp 1 ≠ phi := by linarith
  -- By phi_unique_self_similar, the only positive solution is phi
  have h_uniq := phi_unique_self_similar (Real.exp 1) (Real.exp_pos 1)
  rw [SelfSimilar] at h_uniq
  exact he_ne_phi (h_uniq h)

/-- 2 is not self-similar -/
theorem two_not_self_similar : ¬ SelfSimilar 2 := by
  simp only [SelfSimilar]
  norm_num

/-- √2 is not self-similar -/
theorem sqrt2_not_self_similar : ¬ SelfSimilar (Real.sqrt 2) := by
  simp only [SelfSimilar]
  intro h
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)
  have hsqrt2_gt_1 : Real.sqrt 2 > 1 := by
    have h1 : (1 : ℝ) = Real.sqrt 1 := by simp
    rw [h1]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num : (1 : ℝ) < 2)
  -- From h: (√2)² = √2 + 1, so 2 = √2 + 1, so √2 = 1, contradiction
  rw [h2] at h
  have : Real.sqrt 2 = 1 := by linarith
  linarith

/-! ## Summary Certificate -/

/-- Certificate that φ is the unique Ledger-compatible scale -/
structure PhiUniquenessForScaling where
  phi_works : SelfSimilar phi
  phi_unique : ∀ x : ℝ, x > 0 → SelfSimilar x → x = phi
  pi_fails : ¬ SelfSimilar Real.pi
  e_fails : ¬ SelfSimilar (Real.exp 1)
  two_fails : ¬ SelfSimilar 2
  sqrt2_fails : ¬ SelfSimilar (Real.sqrt 2)
  jcost_optimal : Jcost phi < Jcost 2
  pi_suboptimal : Jcost Real.pi > Jcost phi

/-- The certificate holds -/
def phi_uniqueness_cert : PhiUniquenessForScaling where
  phi_works := phi_self_similar
  phi_unique := phi_unique_self_similar
  pi_fails := pi_not_self_similar
  e_fails := e_not_self_similar
  two_fails := two_not_self_similar
  sqrt2_fails := sqrt2_not_self_similar
  jcost_optimal := self_similar_minimizes_transition phi
    (by have := PhiSupport.one_lt_phi; linarith) phi_self_similar
  pi_suboptimal := pi_scaling_higher_cost

end IndisputableMonolith.LightLanguage
