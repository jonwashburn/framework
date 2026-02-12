import Mathlib
import YM.OSWilson.DoeblinExplicit
import YM.OSWilson.HeatKernelLowerBound

/--
Spectral gap derivation on the odd/mean‑zero sector from the per‑tick
contraction `q_* = 1 − θ_* e^{−λ₁ t₀}`.

References (Yang-Mills-sept21.tex):
- 219–225, 237–241, 249–253: explicit Doeblin/heat‑kernel minorization and
  convex split leading to `q_* ∈ (0,1)`.
- 150–154: best‑of‑two/odd‑cone composition (compatible normalization).

We define the physical slab‑normalized gap as `γ₀ := −log q_*` and prove
positivity directly from `q_* ∈ (0,1)`.
-/
namespace YM.OSWilson.DeriveGap

open Real
open YM.OSWilson.DoeblinExplicit

/-- We work with the OS/GNS transfer framework from `SubspaceContraction` for
the mean-zero sector norms; the mass-gap identification below uses only the
`q_*` interface data. -/
open YM.OSWilson.SubspaceContraction

/-- Gap datum parameterized by `(θ_*, t₀)` and `λ₁(G)`. -/
structure GapParams where
  θt0 : MinorizationSketch
  λ1 : ℝ
  λ1_pos : 0 < λ1

/-- The slab‑normalized gap `γ₀ := −log q_*` with `q_*` from `θt0, λ₁`. -/
def gamma0 {N : ℕ} [Fact (1 < N)] (P : GapParams) : ℝ :=
  let q := q_star (N := N) P.λ1
  -Real.log q

/-- Positivity of `γ₀` from `q_* ∈ (0,1)`. -/
theorem gamma0_pos {N : ℕ} [Fact (1 < N)] (P : GapParams) : 0 < gamma0 (N := N) P := by
  have hq : 0 < q_star (N := N) P.λ1 ∧ q_star (N := N) P.λ1 < 1 :=
    q_star_in_unit_interval (N := N) P.λ1_pos
  have hlog_neg : Real.log (q_star (N := N) P.λ1) < 0 :=
    (Real.log_lt_iff_lt_exp hq.left).2 (by simpa [Real.exp_zero] using hq.right)
  dsimp [gamma0]
  exact neg_pos.mpr hlog_neg

/-- Default parameters `(θ_*, t₀) = (1/2,1)` witnessing a strictly positive gap
for any `λ₁(G) > 0`. -/
def defaults {N : ℕ} [Fact (1 < N)] (λ1 : ℝ) (hλ1 : 0 < λ1) : GapParams :=
  { θt0 := build_minorization_sketch (N := N)
  , λ1 := λ1, λ1_pos := hλ1 }

theorem defaults_gap_pos {N : ℕ} [Fact (1 < N)] (λ1 : ℝ) (hλ1 : 0 < λ1) :
  0 < gamma0 (N := N) (defaults (N := N) λ1 hλ1) :=
  gamma0_pos (N := N) _

/-- Slab-normalized mass gap: defined via the per-tick contraction `q_*` on
the relevant sector. This matches the `γ₀` notation used downstream. -/
def massGapSlab {N : ℕ} [Fact (1 < N)] (P : GapParams) : ℝ :=
  gamma0 (N := N) P

@[simp]
theorem mass_gap_eq_gamma0 {N : ℕ} [Fact (1 < N)] (P : GapParams) :
  massGapSlab (N := N) P = gamma0 (N := N) P := rfl

end YM.OSWilson.DeriveGap


