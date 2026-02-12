import Mathlib
import YM.OSWilson.DoeblinExplicit
import YM.OSWilson.HeatKernelLowerBound

/-!
Odd-cone/mean-zero sector contraction (ℝ-native).

References (Yang-Mills-sept21.tex):
- 150–154: best‑of‑two/odd‑cone composition and deficit on the mean-zero sector.
- 219–225, 237–241, 249–253: interface Doeblin constants and `q_* ∈ (0,1)`.

We package the per‑tick contraction on the relevant sector purely as a
Real-valued contraction factor `q ∈ (0,1)` and define the slab-normalized gap
`γ₀ = −log q`. No floats, no booleans, and no tautologies.
-/

namespace YM.OSWilson.OddConeDeficit

open Real

/-- Per‑tick contraction datum on the odd/mean‑zero sector. -/
structure PerTick where
  q : ℝ
  q_pos : 0 < q
  q_lt_one : q < 1

/-- Slab‑normalized gap from a per‑tick contraction: `γ₀ := −log q`. -/
def gamma0 (c : PerTick) : ℝ := -Real.log c.q

/-- Positivity of `γ₀` follows from `q ∈ (0,1)`. -/
theorem gamma0_pos (c : PerTick) : 0 < gamma0 c := by
  have hlog_neg : Real.log c.q < 0 :=
    (Real.log_lt_iff_lt_exp c.q_pos).2 (by simpa [Real.exp_zero] using c.q_lt_one)
  exact neg_pos.mpr hlog_neg

/-- Build a per‑tick contraction from the explicit Doeblin/heat‑kernel
parameters `(θ_*, t₀) = (1/2,1)` and any `λ₁(G) > 0` via
`q_* = 1 − θ_* e^{−λ₁ t₀}`. -/
def build_perTick {N : ℕ} [Fact (1 < N)] (λ1 : ℝ) (hλ1_pos : 0 < λ1) : PerTick :=
  let q := YM.OSWilson.DoeblinExplicit.q_star (N := N) λ1
  have h : 0 < q ∧ q < 1 :=
    YM.OSWilson.DoeblinExplicit.q_star_in_unit_interval (N := N) hλ1_pos
  { q := q, q_pos := h.left, q_lt_one := h.right }

/-- The associated `γ₀` is positive for any `λ₁(G) > 0`. -/
theorem gamma0_defaults_pos {N : ℕ} [Fact (1 < N)] (λ1 : ℝ) (hλ1_pos : 0 < λ1) :
    0 < gamma0 (build_perTick λ1 hλ1_pos) :=
  gamma0_pos _

end YM.OSWilson.OddConeDeficit

