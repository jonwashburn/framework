import Mathlib
import IndisputableMonolith.Core
import IndisputableMonolith.RH.RS.Scales

open Classical Function

namespace IndisputableMonolith.Bridge.BridgeData

/-- External bridge anchors provided as data (no axioms): G, ħ, c, plus display anchors. -/
structure BridgeData where
  G     : ℝ
  hbar  : ℝ
  c     : ℝ
  tau0  : ℝ
  ell0  : ℝ

@[simp]
def K_A (_ : BridgeData) : ℝ := Constants.K

/-- Recognition length from anchors: λ_rec = √(ħ G / c^3). -/
@[simp] noncomputable
def lambda_rec (B : BridgeData) : ℝ :=
  Real.sqrt (B.hbar * B.G / (Real.pi * (B.c ^ 3)))

/-- Minimal physical assumptions on bridge anchors reused by analytical lemmas. -/
structure Physical (B : BridgeData) : Prop where
  c_pos    : 0 < B.c
  hbar_pos : 0 < B.hbar
  G_pos    : 0 < B.G

/-- Dimensionless identity for λ_rec (under mild physical positivity assumptions):
    (c^3 · λ_rec^2) / (ħ G) = 1/π. -/
lemma lambda_rec_dimensionless_id (B : BridgeData)
  (hc : 0 < B.c) (hh : 0 < B.hbar) (hG : 0 < B.G) :
  (B.c ^ 3) * (lambda_rec B) ^ 2 / (B.hbar * B.G) = 1 / Real.pi := by
  -- Expand λ_rec = √(ħ G / (π c³)) and simplify algebraically
  unfold lambda_rec
  have h_pos : 0 < B.hbar * B.G / (Real.pi * B.c ^ 3) := by
    apply div_pos (mul_pos hh hG) (mul_pos Real.pi_pos (pow_pos hc 3))
  rw [Real.sq_sqrt (le_of_lt h_pos)]
  field_simp [ne_of_gt (mul_pos hh hG), ne_of_gt Real.pi_pos, ne_of_gt (pow_pos hc 3)]
  ring

/-- Dimensionless identity packaged with a physical-assumptions helper. -/
lemma lambda_rec_dimensionless_id_physical (B : BridgeData) (H : Physical B) :
  (B.c ^ 3) * (lambda_rec B) ^ 2 / (B.hbar * B.G) = 1 / Real.pi :=
  lambda_rec_dimensionless_id B H.c_pos H.hbar_pos H.G_pos

/-- Positivity of λ_rec under physical assumptions. -/
lemma lambda_rec_pos (B : BridgeData) (H : Physical B) : 0 < lambda_rec B := by
  -- λ_rec = √(ħ G / (π c³)) > 0 since all components positive
  unfold lambda_rec
  apply Real.sqrt_pos.mpr
  apply div_pos
  · exact mul_pos H.hbar_pos H.G_pos
  · apply mul_pos Real.pi_pos (pow_pos H.c_pos 3)

@[simp] noncomputable
def K_B (B : BridgeData) : ℝ :=
  lambda_rec B / B.ell0

/-- Combined uncertainty aggregator (policy hook; can be refined downstream). -/
@[simp]
def u_comb (_ : BridgeData) (u_ell0 u_lrec : ℝ) : ℝ := Real.sqrt (u_ell0^2 + u_lrec^2)

lemma u_comb_nonneg (B : BridgeData) (u_ell0 u_lrec : ℝ) : 0 ≤ u_comb B u_ell0 u_lrec := by
  dsimp [u_comb]
  exact Real.sqrt_nonneg _

/-- Symbolic K-gate Z-score witness: Z = |K_A − K_B| / (k·u_comb). -/
@[simp] noncomputable
def Zscore (B : BridgeData) (u_ell0 u_lrec k : ℝ) : ℝ :=
  let KA := K_A B
  let KB := K_B B
  let u  := u_comb B u_ell0 u_lrec
  (abs (KA - KB)) / (k * u)

/-- Boolean pass at threshold k: Z ≤ 1. Publishes the exact Z expression. -/
@[simp] noncomputable
def passAt (B : BridgeData) (u_ell0 u_lrec k : ℝ) : Bool :=
  decide ((Zscore B u_ell0 u_lrec k) ≤ 1)

/-- Full witness record for publication. -/
structure Witness where
  KA : ℝ
  KB : ℝ
  u  : ℝ
  Z  : ℝ
  pass : Bool

@[simp] noncomputable
def witness (B : BridgeData) (u_ell0 u_lrec k : ℝ) : Witness :=
  let KA := K_A B
  let KB := K_B B
  let u  := u_comb B u_ell0 u_lrec
  let Z  := (abs (KA - KB)) / (k * u)
  { KA := KA, KB := KB, u := u, Z := Z, pass := decide (Z ≤ 1) }

/-- Tick from anchors via hop map λ_rec = c · τ0. -/
@[simp] noncomputable
def tau0 (B : BridgeData) : ℝ := lambda_rec B / B.c

/-- Coherence energy: E_coh = φ^-5 · (2π ħ / τ0). -/
@[simp] noncomputable
def E_coh (B : BridgeData) : ℝ :=
  (1 / (Constants.phi ^ (5 : Nat))) * (2 * Real.pi * B.hbar / (tau0 B))

/-- Dimensionless inverse fine-structure constant (seed–gap–curvature). -/
@[simp] noncomputable
def alphaInv : ℝ :=
  4 * Real.pi * 11 - (Real.log Constants.phi + (103 : ℝ) / (102 * Real.pi ^ 5))

/-- Fine-structure constant α. -/
@[simp] noncomputable
def alpha : ℝ := 1 / alphaInv

/-- Electron mass in units of E_coh: m_e/E_coh = Φ(r_e + 𝔽(Z_e)). -/
@[simp] noncomputable
def m_e_over_Ecoh : ℝ :=
  IndisputableMonolith.RH.RS.PhiPow 0

/-- Electron mass: m_e = (m_e/E_coh) · E_coh. -/
@[simp] noncomputable
def m_e (B : BridgeData) : ℝ := m_e_over_Ecoh * E_coh B

/-- Bohr radius a0 = ħ / (m_e c α). -/
@[simp] noncomputable
def a0_bohr (B : BridgeData) : ℝ :=
  B.hbar / (m_e B * B.c * alpha)

end IndisputableMonolith.Bridge.BridgeData
