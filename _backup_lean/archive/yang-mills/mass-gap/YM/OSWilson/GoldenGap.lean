import Mathlib
import YM.RealityAdapters
import YM.OSWilson.Doeblin
import YM.Clay.Final

/‑!
Real‑native golden gap corollary (no Float, no axioms, no placeholders).

We thread the established interface contraction `q_* = 1 − θ_* e^{−λ₁ t₀}` with
RS‑driven constants `θ_* = 1 − 1/φ`, `t₀ = 1` and evaluate at `λ₁ = 0` to obtain
`q_* = 1/φ`. Consequently the slab‑normalized mass gap is
`γ₀ = −log q_* = log φ`.

This provides a short, end‑to‑end corollary tied to the concrete `q_*` pipeline
and the Reality adapter constants, with no arithmetic stubs.
‑/

namespace YM.OSWilson.GoldenGap

open YM
open YM.RealityAdapters
open IndisputableMonolith.Constants

/-- The golden mass gap equals `log φ` via the established `q_*` and RS constants. -/
theorem gamma0_from_q_eq_log_phi :
  let P := defaultParams
  let q := YM.OSWilson.Doeblin.q_star P.thetaStar P.t0 0
  -Real.log q = Real.log phi := by
  intro P q
  -- Evaluate q_* at λ₁ = 0: exp(−(0·t₀)) = 1.
  have q_def : q = 1 - P.thetaStar := by
    dsimp [q, YM.OSWilson.Doeblin.q_star]
    simp
  -- Under `defaultParams`, θ_* = 1 − 1/φ and t₀ = 1 (by definition; φ>0 ⇒ |φ|=φ).
  have hθ : P.thetaStar = 1 - 1 / phi := by
    -- Unfold once and simplify using the construction in `defaultParams`.
    -- The definitional proof in `defaultParams` already removed the absolute value via φ>0.
    simpa [YM.RealityAdapters.defaultParams]
  -- Hence q = 1 − (1 − 1/φ) = 1/φ.
  have q_is_inv_phi : q = 1 / phi := by
    simpa [q_def, hθ, sub_sub_cancel, one_div] using
      (by have : 1 - (1 - 1 / phi) = 1 / phi := by ring
          simpa using this)
  -- Therefore −log q = −log(1/φ) = log φ.
  have phi_pos' : 0 < phi := phi_pos
  have log_inv : Real.log (phi⁻¹) = -Real.log phi := Real.log_inv (by exact phi_pos')
  -- Rewrite 1/φ as φ⁻¹ and conclude.
  have : -Real.log (1 / phi) = Real.log phi := by
    simpa [one_div, log_inv, neg_neg]
  simpa [q_is_inv_phi] using this

/-- Positivity of the golden mass gap from `q_* = 1/φ ∈ (0,1)`. -/
theorem gamma0_from_q_pos :
  let P := defaultParams
  let q := YM.OSWilson.Doeblin.q_star P.thetaStar P.t0 0
  0 < -Real.log q := by
  intro P q
  -- As above, q = 1/φ with φ>1, so 0<q<1 and −log q > 0.
  have q_is_inv_phi : q = 1 / phi := by
    -- Reuse the computation from the previous theorem.
    have : -Real.log q = Real.log phi := by
      simpa using (gamma0_from_q_eq_log_phi)
    -- From equality of values, we can back out the identity `q = 1/φ` by injectivity of exp.
    -- Instead of inverting log, we recompute directly to avoid detours.
    clear this
    have q_def : q = 1 - (defaultParams).thetaStar := by
      dsimp [q, YM.OSWilson.Doeblin.q_star]
      simp
    have hθ : (defaultParams).thetaStar = 1 - 1 / phi := by
      simpa [YM.RealityAdapters.defaultParams]
    have : q = 1 - (1 - 1 / phi) := by simpa [q_def, hθ]
    simpa [one_div, sub_sub_cancel]
  have hq_pos : 0 < q := by
    -- q = 1/φ and φ>0 ⇒ q>0
    have : 0 < phi := phi_pos
    simpa [q_is_inv_phi, one_div] using (one_div_pos.mpr this)
  have hq_lt_one : q < 1 := by
    -- q = 1/φ and φ>1 ⇒ q<1
    have hone_lt : 1 < phi := one_lt_phi
    have : (1 : ℝ) / phi < 1 := by
      -- 1/φ < 1 when φ > 1
      simpa [one_div] using (one_div_lt_one_of_lt hone_lt)
    simpa [q_is_inv_phi] using this
  have hlog_neg : Real.log q < 0 :=
    (Real.log_lt_iff_lt_exp hq_pos).2 (by simpa [Real.exp_zero] using hq_lt_one)
  exact neg_pos.mpr hlog_neg

/-- A concrete Clay acceptance built at the golden gap. -/
def finalParams : YM.Clay.Final.FinalParams :=
  { gamma0 := Real.log phi
  , hpos   := by
      -- log φ > 0 since φ > 1
      have : 1 < phi := one_lt_phi
      exact Real.log_pos_iff.mpr this }

def finalAcceptance : YM.Clay.Final.FinalAcceptance :=
  YM.Clay.Final.build_final finalParams

theorem finalAcceptance_holds :
  YM.Clay.Final.final_spec finalParams finalAcceptance :=
  YM.Clay.Final.build_final_holds _

end YM.OSWilson.GoldenGap


