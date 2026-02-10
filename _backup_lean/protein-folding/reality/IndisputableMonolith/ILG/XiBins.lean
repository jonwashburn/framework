import Mathlib

namespace IndisputableMonolith
namespace ILG

noncomputable section
open Real

/-! Dependency-light ILG helpers: n_of_r and xi_of_bin. -/

@[simp] def εr : ℝ := 1e-12

/-- Analytic global radial shape factor n(r) = 1 + A (1 - exp(-(r/r0)^p)). -/
@[simp] noncomputable def n_of_r (A r0 p : ℝ) (r : ℝ) : ℝ :=
  let x := (max 0 r) / max εr r0
  1 + A * (1 - Real.exp (-(x ^ p)))

/-- Monotonicity in A under nonnegative exponent. -/
lemma n_of_r_mono_A_of_nonneg_p {A1 A2 r0 p r : ℝ}
  (hp : 0 ≤ p) (hA12 : A1 ≤ A2) :
  n_of_r A1 r0 p r ≤ n_of_r A2 r0 p r := by
  simp only [n_of_r, εr]
  set x := (max 0 r) / max (1e-12 : ℝ) r0 with hx
  have hden_pos : 0 < max (1e-12 : ℝ) r0 := by
    have heps : (0 : ℝ) < 1e-12 := by norm_num
    exact lt_max_of_lt_left heps
  have hbase_nonneg : 0 ≤ (max 0 r) / max (1e-12 : ℝ) r0 := by
    have : 0 ≤ max 0 r := le_max_left _ _
    exact div_nonneg this (le_of_lt hden_pos)
  have hx_nonneg : 0 ≤ x := hbase_nonneg
  have hx_pow_nonneg : 0 ≤ x ^ p := Real.rpow_nonneg hx_nonneg _
  have hterm_nonneg : 0 ≤ 1 - Real.exp (-(x ^ p)) := by
    have hneg : -(x ^ p) ≤ 0 := neg_nonpos.mpr hx_pow_nonneg
    have : Real.exp (-(x ^ p)) ≤ 1 := Real.exp_le_one_iff.mpr hneg
    exact sub_nonneg.mpr this
  have hmul : A1 * (1 - Real.exp (-(x ^ p))) ≤ A2 * (1 - Real.exp (-(x ^ p))) :=
    mul_le_mul_of_nonneg_right hA12 hterm_nonneg
  linarith

/-- Threads-informed global factor ξ from bin-center u ∈ [0,1]. -/
@[simp] noncomputable def xi_of_u (u : ℝ) : ℝ := 1 + Real.sqrt (max 0 (min 1 u))

/-- Deterministic bin centers for global-only ξ (quintiles). -/
@[simp] noncomputable def xi_of_bin : Nat → ℝ
| 0 => xi_of_u 0.1
| 1 => xi_of_u 0.3
| 2 => xi_of_u 0.5
| 3 => xi_of_u 0.7
| _ => xi_of_u 0.9

/-- Monotonicity over the canonical quintile bin centers. -/
lemma xi_of_bin_mono : xi_of_bin 0 ≤ xi_of_bin 1 ∧ xi_of_bin 1 ≤ xi_of_bin 2 ∧
  xi_of_bin 2 ≤ xi_of_bin 3 ∧ xi_of_bin 3 ≤ xi_of_bin 4 := by
  -- xi_of_u is monotone in u on [0,1] because sqrt and max/min are monotone
  have mono_xi : Monotone xi_of_u := by
    intro u v huv
    dsimp [xi_of_u]
    -- Clamp values are monotone in the input
    have hclamp : max 0 (min 1 u) ≤ max 0 (min 1 v) := by
      apply max_le_max (le_refl 0)
      exact min_le_min_left 1 huv
    have h0u : 0 ≤ max 0 (min 1 u) := le_max_left _ _
    have h0v : 0 ≤ max 0 (min 1 v) := le_max_left _ _
    have hsqrt := Real.sqrt_le_sqrt hclamp
    exact add_le_add_left hsqrt 1
  have h12 : (0.1 : ℝ) ≤ 0.3 := by norm_num
  have h23 : (0.3 : ℝ) ≤ 0.5 := by norm_num
  have h34 : (0.5 : ℝ) ≤ 0.7 := by norm_num
  have h45 : (0.7 : ℝ) ≤ 0.9 := by norm_num
  have h0 := mono_xi h12
  have h1 := mono_xi h23
  have h2 := mono_xi h34
  have h3 := mono_xi h45
  dsimp [xi_of_bin] at h0 h1 h2 h3
  exact ⟨h0, h1, h2, h3⟩

end
end ILG
end IndisputableMonolith
