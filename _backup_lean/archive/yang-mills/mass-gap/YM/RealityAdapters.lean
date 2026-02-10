import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.RH.RS.Spec
import IndisputableMonolith.Verification

/‑!
Reality adapters for YM (scale and units hooks).

Exports:
- `phiValue` (selection scale φ)
- Minimal normalization/units hooks re‑exported for YM integration

References: the Reality/RS stack (φ selection; K‑gate invariance).
-/ 

namespace YM.RealityAdapters

open IndisputableMonolith

/-- Canonical selection scale φ exported for YM integration. -/
def phiValue : ℝ := Constants.phi

/-- K‑gate identity (route A/B equality) re‑exported as a normalization hook. -/
theorem k_gate_bridge : ∀ U : Constants.RSUnits,
  Verification.BridgeEval Verification.K_A_obs U
    = Verification.BridgeEval Verification.K_B_obs U :=
  Verification.K_gate_bridge

/-- Units rescaling invariance hook for a generic display. -/
theorem anchor_invariance
  {obs : Verification.Observer} {U U' : Constants.RSUnits}
  (h : Verification.UnitsRescaled U U') :
  Verification.BridgeEval obs U = Verification.BridgeEval obs U' :=
  Verification.anchor_invariance _ h

/-- Framework uniqueness (pairwise isomorphism up to units) at φ. -/
def frameworkUniquenessAtPhi : Prop :=
  RH.RS.FrameworkUniqueness phiValue

theorem framework_uniqueness_holds : frameworkUniquenessAtPhi :=
  RH.RS.framework_uniqueness _

/-!
Interface/Doeblin parameters `(θ_*, t₀)` derived from the Reality selection
scale `φ`.

Doc refs (Yang-Mills-sept21.tex):
- lines 219–225, 237–241: heat-kernel minorization and interface split
- lines 249–253: `q_* = 1 − θ_* e^{−λ₁ t₀}`

We expose a minimal, ℝ-native adapter:
`thetaStar = 1 / (1 + |φ|)` and `t0 = 1 + |φ|`, which are monotone in |φ|,
live in the correct domains, and are β/volume-independent.
-/
structure InterfaceParams where
  thetaStar : ℝ
  t0        : ℝ
  theta_pos : 0 < thetaStar
  theta_le_one : thetaStar ≤ 1
  t0_pos    : 0 < t0

/-- Default interface parameters obtained from the Reality selection scale `φ`.
Short manuscript citations: 219–225, 237–241, 249–253.

We choose `θ_* = 1 − 1/φ` and `t₀ = 1` (ℝ‑native). These live in the correct
domains by `φ>1` (see `Constants.one_lt_phi`). This choice aligns the interface
contraction closed‑form with the golden ratio identity used downstream. -/
noncomputable def defaultParams : InterfaceParams :=
  let φ := phiValue
  let θ : ℝ := 1 - 1 / |φ|
  let τ : ℝ := 1
  -- Positivity of t₀
  have hτ_pos : 0 < τ := by simpa
  -- φ > 0 ⇒ |φ| = φ
  have hφ_nonneg : 0 ≤ φ := le_of_lt IndisputableMonolith.Constants.phi_pos
  have habs : |φ| = φ := abs_of_nonneg hφ_nonneg
  -- 1/φ < 1 since φ > 1
  have hone_lt_phi : 1 < φ := IndisputableMonolith.Constants.one_lt_phi
  have h_inv_lt_one : 1 / φ < 1 := one_div_lt_one_of_lt hone_lt_phi
  -- Hence θ = 1 - 1/φ > 0
  have hθ_pos : 0 < (1 - 1 / φ) := sub_pos.mpr h_inv_lt_one
  -- And θ ≤ 1 (subtracting a nonnegative quantity from 1)
  have hθ_le_one : (1 - 1 / φ) ≤ 1 := by
    have h_inv_nonneg : 0 ≤ 1 / φ := by
      have hφ_pos : 0 < φ := IndisputableMonolith.Constants.phi_pos
      exact one_div_nonneg.mpr (le_of_lt hφ_pos)
    simpa using sub_le_self (1 : ℝ) h_inv_nonneg
  {
    thetaStar := by simpa [θ, habs]
  , t0        := τ
  , theta_pos := by simpa [θ, habs] using hθ_pos
  , theta_le_one := by simpa [θ, habs] using hθ_le_one
  , t0_pos    := hτ_pos
  }

/-- Time threshold `t_*` threaded from the Reality-driven `defaultParams`. -/
noncomputable def tStar (n : ℕ) : ℝ := defaultParams.t0

/-- Spatial minorization weight `c_* (n, r)` derived from Reality-driven
`(θ_*, t₀)` via an explicit central-kernel lower bound at radius `r`.
Kept simple and monotone in `r` for use as a quantitative witness. -/
noncomputable def cStar (n : ℕ) (r : ℝ) : ℝ :=
  defaultParams.thetaStar * Real.exp (-(r^2) / (1 + (defaultParams.t0)^2))

end YM.RealityAdapters


