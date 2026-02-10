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
  dsimp [n_of_r]
  set x := (max 0 r) / max εr r0 with hx
  have hden_pos : 0 < max εr r0 := by
    have : 0 < εr := by
      have : (1e-12 : ℝ) > 0 := by norm_num
      simpa [εr] using this
    exact lt_max_of_lt_left this
  have hbase_nonneg : 0 ≤ (max 0 r) / max εr r0 := by
    have : 0 ≤ max 0 r := le_max_left _ _
    exact div_nonneg this (le_of_lt hden_pos)
  have hx_nonneg : 0 ≤ x := by simpa [hx] using hbase_nonneg
  have hx_pow_nonneg : 0 ≤ x ^ p := Real.rpow_nonneg hx_nonneg hp
  have hterm_nonneg : 0 ≤ 1 - Real.exp (-(x ^ p)) := by
    have : Real.exp (-(x ^ p)) ≤ 1 := by
      have : -(x ^ p) ≤ 0 := by exact neg_nonpos.mpr hx_pow_nonneg
      exact Real.exp_le_one_of_nonpos this
    exact sub_nonneg.mpr this
  have : A1 * (1 - Real.exp (-(x ^ p))) ≤ A2 * (1 - Real.exp (-(x ^ p))) :=
    mul_le_mul_of_nonneg_right hA12 hterm_nonneg
  simpa [hx, add_comm, add_left_comm, add_assoc]
    using add_le_add_left this 1

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
    have hclamp : max 0 (min 1 u) ≤ max 0 (min 1 v) := by
      exact max_le_max (le_of_eq rfl) (min_le_min_right (le_of_lt ?_))
    -- Provide a simple bound using basic facts: since 0 ≤ max 0 (min 1 u) ≤ max 0 (min 1 v)
    -- and sqrt is monotone on ℝ≥0
    have h0u : 0 ≤ max 0 (min 1 u) := le_max_left _ _
    have h0v : 0 ≤ max 0 (min 1 v) := le_max_left _ _
    have hsqrt := Real.sqrt_le_sqrt_iff.mpr hclamp
    exact add_le_add_left hsqrt 1
  have h01 : (0 : ℝ) ≤ 0.1 := by norm_num
  have h12 : (0.1 : ℝ) ≤ 0.3 := by norm_num
  have h23 : (0.3 : ℝ) ≤ 0.5 := by norm_num
  have h34 : (0.5 : ℝ) ≤ 0.7 := by norm_num
  have h45 : (0.7 : ℝ) ≤ 0.9 := by norm_num
  have h0 := mono_xi (by exact h12)
  have h1 := mono_xi (by exact h23)
  have h2 := mono_xi (by exact h34)
  have h3 := mono_xi (by exact h45)
  dsimp [xi_of_bin] at h0 h1 h2 h3
  exact And.intro h0 (And.intro h1 (And.intro h2 h3))

end
end ILG
end IndisputableMonolith
