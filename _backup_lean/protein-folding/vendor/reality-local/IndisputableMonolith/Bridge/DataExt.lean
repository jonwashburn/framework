import Mathlib
import IndisputableMonolith.Core
import IndisputableMonolith.Constants
import IndisputableMonolith.RH.RS.Scales
import IndisputableMonolith.Bridge.Data

/-!
Bridge Data Physical Constants and K-Gate Verification

This module re-exports lightweight helpers for bridge displays while
keeping all canonical definitions in `Bridge/Data.lean`.
-/

namespace IndisputableMonolith
namespace Bridge
namespace DataExt

open IndisputableMonolith.BridgeData

@[simp] def u_comb (B : BridgeData) (u_ell0 u_lrec : ℝ) : ℝ :=
  Real.sqrt (u_ell0^2 + u_lrec^2)

@[simp] def Zscore (B : BridgeData) (u_ell0 u_lrec k : ℝ) : ℝ :=
  let KA := K_A B; let KB := K_B B; let u := u_comb B u_ell0 u_lrec
  (Real.abs (KA - KB)) / (k * u)

@[simp] noncomputable def passAt (B : BridgeData) (u_ell0 u_lrec k : ℝ) : Bool :=
  decide ((Zscore B u_ell0 u_lrec k) ≤ 1)

structure Witness where
  KA : ℝ
  KB : ℝ
  u  : ℝ
  Z  : ℝ
  pass : Bool

@[simp] noncomputable def witness (B : BridgeData) (u_ell0 u_lrec k : ℝ) : Witness :=
  let KA := K_A B
  let KB := K_B B
  let u  := u_comb B u_ell0 u_lrec
  let Z  := (Real.abs (KA - KB)) / (k * u)
  { KA := KA, KB := KB, u := u, Z := Z, pass := decide (Z ≤ 1) }

@[simp] noncomputable def tick_tau0 (B : BridgeData) : ℝ := lambda_rec B / B.c

@[simp] noncomputable def E_coh (B : BridgeData) : ℝ :=
  (1 / (Constants.phi ^ (5 : Nat))) * (2 * Real.pi * B.hbar / (tick_tau0 B))

@[simp] noncomputable def alphaInv : ℝ :=
  4 * Real.pi * 11 -
    (Real.log Constants.phi + (103 : ℝ) / (102 * Real.pi ^ 5))

@[simp] noncomputable def alpha : ℝ := 1 / alphaInv

@[simp] noncomputable def m_e_over_Ecoh : ℝ :=
  RH.RS.PhiPow (0 : ℝ)

@[simp] noncomputable def m_e (B : BridgeData) : ℝ := m_e_over_Ecoh * E_coh B

@[simp] noncomputable def a0_bohr (B : BridgeData) : ℝ :=
  B.hbar / (m_e B * B.c * alpha)

end DataExt
end Bridge
end IndisputableMonolith
