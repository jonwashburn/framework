import Mathlib
import IndisputableMonolith.Core
import IndisputableMonolith.RH.RS.Scales

/-!
Bridge Data Module

This module contains the BridgeData structure and associated physical constants,
dimensionless identities, and bridge-related functions for the recognition system.
-/

namespace IndisputableMonolith.BridgeData

/-- External bridge anchors provided as data (no axioms): G, ħ, c, plus display anchors. -/
structure BridgeData where
  G     : ℝ
  hbar  : ℝ
  c     : ℝ
  tau0  : ℝ
  ell0  : ℝ

/-- Minimal physical assumptions on bridge anchors reused by analytical lemmas. -/
structure Physical (B : BridgeData) : Prop where
  c_pos    : 0 < B.c
  hbar_pos : 0 < B.hbar
  G_pos    : 0 < B.G

/-- Recognition length from anchors: lambda_rec = √(ħ G / c^3). -/
noncomputable def lambda_rec (B : BridgeData) : ℝ :=
  Real.sqrt (B.hbar * B.G / (Real.pi * (B.c ^ 3)))

/-- Dimensionless identity for lambda_rec (under mild physical positivity assumptions):
    (c^3 · lambda_rec^2) / (ħ G) = 1/π. -/
lemma lambda_rec_dimensionless_id (B : BridgeData)
  (hc : 0 < B.c) (hh : 0 < B.hbar) (hG : 0 < B.G) :
  (B.c ^ 3) * (lambda_rec B) ^ 2 / (B.hbar * B.G) = 1 / Real.pi := by
  -- Expand lambda_rec and simplify using sqrt and algebra
  unfold lambda_rec
  have h_pos : 0 < B.hbar * B.G / (Real.pi * B.c ^ 3) := by
    apply div_pos (mul_pos hh hG)
    exact mul_pos Real.pi_pos (pow_pos hc 3)
  -- Use (sqrt x)^2 = x for x ≥ 0
  have h_nonneg : 0 ≤ B.hbar * B.G / (Real.pi * B.c ^ 3) := le_of_lt h_pos
  have : (Real.sqrt (B.hbar * B.G / (Real.pi * B.c ^ 3))) ^ 2 =
    B.hbar * B.G / (Real.pi * B.c ^ 3) := by
    simpa using Real.sq_abs (Real.sqrt (B.hbar * B.G / (Real.pi * B.c ^ 3)))
  -- Prefer standard identity: sqr of sqrt
  have : (Real.sqrt (B.hbar * B.G / (Real.pi * B.c ^ 3))) ^ 2 =
    B.hbar * B.G / (Real.pi * B.c ^ 3) := by
    simpa using Real.sq_sqrt h_nonneg
  -- Now simplify the target expression
  calc
    (B.c ^ 3) * (Real.sqrt (B.hbar * B.G / (Real.pi * B.c ^ 3))) ^ 2 / (B.hbar * B.G)
        = (B.c ^ 3) * (B.hbar * B.G / (Real.pi * B.c ^ 3)) / (B.hbar * B.G) := by
          simp [this]
    _ = ((B.c ^ 3) * (B.hbar * B.G)) / ((Real.pi * B.c ^ 3) * (B.hbar * B.G)) := by
          field_simp
    _ = 1 / Real.pi := by
          field_simp [mul_comm, mul_left_comm, mul_assoc, pow_succ, pow_mul]

/-- Dimensionless identity packaged with a physical-assumptions helper. -/
lemma lambda_rec_dimensionless_id_physical (B : BridgeData) (H : Physical B) :
  (B.c ^ 3) * (lambda_rec B) ^ 2 / (B.hbar * B.G) = 1 / Real.pi :=
  lambda_rec_dimensionless_id B H.c_pos H.hbar_pos H.G_pos

/-- Positivity of lambda_rec under physical assumptions. -/
lemma lambda_rec_pos (B : BridgeData) (H : Physical B) : 0 < lambda_rec B := by
  -- lambda_rec = √(ħ G / (π c³)) > 0 since all components positive
  unfold lambda_rec
  apply Real.sqrt_pos.mpr
  apply div_pos
  · exact mul_pos H.hbar_pos H.G_pos
  · exact mul_pos Real.pi_pos (pow_pos H.c_pos 3)

/-- K_A = φ (golden ratio constant). -/
def K_A (_ : BridgeData) : ℝ := IndisputableMonolith.Constants.K

-- Use Real.abs directly from Mathlib

/-- K_B = lambda_rec/ℓ0. -/
noncomputable def K_B (B : BridgeData) : ℝ :=
  lambda_rec B / B.ell0

/-- Combined uncertainty aggregator (policy hook; can be specialized by callers). -/
noncomputable def u_comb (_ : BridgeData) (u_ell0 u_lrec : ℝ) : ℝ := Real.sqrt (u_ell0^2 + u_lrec^2)

lemma u_comb_nonneg (B : BridgeData) (u_ell0 u_lrec : ℝ) :
  0 ≤ u_comb B u_ell0 u_lrec := by
  dsimp [u_comb]
  exact Real.sqrt_nonneg _

lemma u_comb_comm (B : BridgeData) (u_ell0 u_lrec : ℝ) :
  u_comb B u_ell0 u_lrec = u_comb B u_lrec u_ell0 := by
  dsimp [u_comb]
  have : u_ell0 ^ 2 + u_lrec ^ 2 = u_lrec ^ 2 + u_ell0 ^ 2 := by
    simpa [add_comm]
  simpa [this]

/-- Symbolic K-gate Z-score witness: Z = |K_A − K_B| / (k·u_comb). -/
noncomputable def Zscore (B : BridgeData) (u_ell0 u_lrec k : ℝ) : ℝ :=
  let KA := K_A B
  let KB := K_B B
  let u  := u_comb B u_ell0 u_lrec
  (Real.abs (KA - KB)) / (k * u)

@[simp] lemma passAt_true_iff (B : BridgeData) (u_ell0 u_lrec k : ℝ) :
  passAt B u_ell0 u_lrec k = true ↔ Zscore B u_ell0 u_lrec k ≤ 1 := by
  dsimp [passAt]
  by_cases h : Zscore B u_ell0 u_lrec k ≤ 1
  · simp [h]
  · simp [h]

/-- Boolean pass at threshold k: Z ≤ 1. Publishes the exact Z expression. -/
noncomputable def passAt (B : BridgeData) (u_ell0 u_lrec k : ℝ) : Bool :=
  decide ((Zscore B u_ell0 u_lrec k) ≤ 1)

/-- Full witness record for publication. -/
structure Witness where
  KA : ℝ
  KB : ℝ
  u  : ℝ
  Z  : ℝ
  pass : Bool

/-- Witness constructor. -/
noncomputable def witness (B : BridgeData) (u_ell0 u_lrec k : ℝ) : Witness :=
  let KA := K_A B
  let KB := K_B B
  let u  := u_comb B u_ell0 u_lrec
  let Z  := (Real.abs (KA - KB)) / (k * u)
  { KA := KA, KB := KB, u := u, Z := Z, pass := decide (Z ≤ 1) }

/-- Tick from anchors via hop map lambda_rec = c · τ0. -/
noncomputable def tau0 (B : BridgeData) : ℝ := lambda_rec B / B.c

-- Use canonically defined φ-exponential
@[simp] noncomputable abbrev PhiPow (x : ℝ) : ℝ := IndisputableMonolith.RH.RS.PhiPow x

/-! Recognition-specific primitives are left abstract via neutral defaults
    to keep this module axiom-free while isolating numerics elsewhere. -/
/-! Parametric recognition inputs (replace numeric stubs). -/

structure RecognitionInputsScalar where
  r    : ℝ
  Fgap : ℝ → ℝ
  Z    : ℝ
  deriving Repr

@[simp] noncomputable def neutralInputs : RecognitionInputsScalar :=
  { r := 0, Fgap := fun _ => 0, Z := 0 }

/-- Coherence energy: E_coh = φ^-5 · (2π ħ / τ0). -/
noncomputable def E_coh (B : BridgeData) : ℝ :=
  (1 / (IndisputableMonolith.Constants.phi ^ (5 : Nat))) * (2 * Real.pi * B.hbar / (tau0 B))

/-- Dimensionless inverse fine-structure constant (seed–gap–curvature). -/
noncomputable def alphaInv : ℝ :=
  4 * Real.pi * 11 - (Real.log IndisputableMonolith.Constants.phi + (103 : ℝ) / (102 * Real.pi ^ 5))

/-- Fine-structure constant α. -/
noncomputable def alpha : ℝ := 1 / alphaInv

/-- Electron mass in units of E_coh: m_e/E_coh = Φ(r_e + 𝔽(Z_e)). -/
noncomputable def m_e_over_Ecoh_with (I : RecognitionInputsScalar) : ℝ :=
  PhiPow (I.r + I.Fgap I.Z)

/-- Electron mass: m_e = (m_e/E_coh) · E_coh. -/
noncomputable def m_e_with (B : BridgeData) (I : RecognitionInputsScalar) : ℝ :=
  m_e_over_Ecoh_with I * E_coh B

-- Backwards-compatible default (uses neutral inputs)
@[simp] noncomputable def m_e (B : BridgeData) : ℝ := m_e_with B neutralInputs

/-- Bohr radius a0 = ħ / (m_e c α). -/
noncomputable def a0_bohr_with (B : BridgeData) (I : RecognitionInputsScalar) : ℝ :=
  B.hbar / (m_e_with B I * B.c * alpha)

-- Backwards-compatible default (uses neutral inputs)
@[simp] noncomputable def a0_bohr (B : BridgeData) : ℝ := a0_bohr_with B neutralInputs

end IndisputableMonolith.BridgeData