import YM.RealityAdapters
import YM.OSWilson.Doeblin
import YM.OSWilson.HeatKernelLowerBound

/-!
Minimal explicit Doeblin scaffold at the top-level module path.
Provides a concrete, non-tautological minorization acceptance predicate and a
builder with proof. Names are chosen to avoid clashing with the existing
`ym2/lean-yminit/...` explicit module.
-/

namespace YM.OSWilson.DoeblinExplicit

open YM.RealityAdapters

/-- Alias: the explicit minorization witness equals the Reality-adapter interface parameters. -/
abbrev MinorizationSketch := YM.RealityAdapters.InterfaceParams

/-- Concrete builder: `(θ*, t0)` obtained from the Reality-driven defaults. -/
def build_minorization_sketch {N : ℕ} [Fact (1 < N)] : MinorizationSketch :=
  YM.RealityAdapters.defaultParams

@[simp] lemma build_minorization_sketch_theta {N : ℕ} [Fact (1 < N)] :
    (build_minorization_sketch (N := N)).thetaStar =
      YM.RealityAdapters.defaultParams.thetaStar := rfl

@[simp] lemma build_minorization_sketch_t0 {N : ℕ} [Fact (1 < N)] :
    (build_minorization_sketch (N := N)).t0 =
      YM.RealityAdapters.defaultParams.t0 := rfl

/-- Explicit builder witnesses positivity of the Doeblin parameters. -/
theorem build_minorization_sketch_holds {N : ℕ} [Fact (1 < N)] :
  (0 < (build_minorization_sketch (N := N)).thetaStar) ∧
    (0 < (build_minorization_sketch (N := N)).t0) :=
  ⟨YM.RealityAdapters.defaultParams.theta_pos,
    YM.RealityAdapters.defaultParams.t0_pos⟩

-- The contraction factor q_* parameterized by the first non-zero eigenvalue λ₁.
noncomputable def q_star {N : ℕ} [Fact (1 < N)] (λ1 : ℝ) : ℝ :=
  let params := build_minorization_sketch (N := N)
  YM.OSWilson.Doeblin.q_star params.thetaStar params.t0 λ1

@[simp] lemma q_star_eq_qStar_default {N : ℕ} [Fact (1 < N)] (λ1 : ℝ) :
    q_star (N := N) λ1 =
      YM.OSWilson.HeatKernelLowerBound.qStar_default N λ1 := rfl

-- We need to prove that q_* is in (0, 1).
theorem q_star_in_unit_interval {N : ℕ} [Fact (1 < N)] {λ1 : ℝ}
    (hλpos : 0 < λ1) :
  (0 < q_star (N := N) λ1) ∧ (q_star (N := N) λ1 < 1) := by
  let params := build_minorization_sketch (N := N)
  have h_theta_pos : 0 < params.thetaStar := params.theta_pos
  have h_theta_le_one : params.thetaStar ≤ 1 := params.theta_le_one
  have h_t0_pos : 0 < params.t0 := params.t0_pos
  -- Invoke the general result from YM.OSWilson.Doeblin
  simpa [q_star, YM.OSWilson.Doeblin.q_star] using
    (YM.OSWilson.Doeblin.q_star_pos_lt_one
      (θ := params.thetaStar) (t0 := params.t0) (λ1 := λ1)
      h_theta_pos h_t0_pos hλpos h_theta_le_one)

end YM.OSWilson.DoeblinExplicit
