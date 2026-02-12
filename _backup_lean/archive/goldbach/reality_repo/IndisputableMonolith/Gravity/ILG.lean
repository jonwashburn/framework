import Mathlib

namespace IndisputableMonolith
namespace Gravity
namespace ILG

noncomputable section
open Real

/-! Minimal extracted time-kernel basics with parametric interfaces. -/

structure BridgeData where
  tau0 : ℝ

structure BaryonCurves where
  vgas  : ℝ → ℝ
  vdisk : ℝ → ℝ
  vbul  : ℝ → ℝ

/-! Configurable numeric regularization parameters. -/
structure Config where
  upsilonStar : ℝ
  eps_r : ℝ
  eps_v : ℝ
  eps_t : ℝ
  eps_a : ℝ
  deriving Repr

@[simp] def defaultConfig : Config :=
  { upsilonStar := 1.0
  , eps_r := 1e-12
  , eps_v := 1e-12
  , eps_t := 1e-12
  , eps_a := 1e-12 }

structure ConfigProps (cfg : Config) : Prop where
  eps_t_le_one : cfg.eps_t ≤ 1

@[simp] lemma defaultConfig_props : ConfigProps defaultConfig := by
  refine ⟨?h⟩
  norm_num

def vbarSq_with (cfg : Config) (C : BaryonCurves) (r : ℝ) : ℝ :=
  max 0 ((C.vgas r) ^ 2 + ((Real.sqrt cfg.upsilonStar) * (C.vdisk r)) ^ 2 + (C.vbul r) ^ 2)

def vbar_with (cfg : Config) (C : BaryonCurves) (r : ℝ) : ℝ :=
  Real.sqrt (max cfg.eps_v (vbarSq_with cfg C r))

def gbar_with (cfg : Config) (C : BaryonCurves) (r : ℝ) : ℝ :=
  (vbar_with cfg C r) ^ 2 / max cfg.eps_r r

structure Params where
  alpha      : ℝ
  Clag       : ℝ
  A          : ℝ
  r0         : ℝ
  p          : ℝ
  hz_over_Rd : ℝ

structure ParamProps (P : Params) : Prop where
  alpha_nonneg : 0 ≤ P.alpha
  Clag_nonneg  : 0 ≤ P.Clag
  Clag_le_one  : P.Clag ≤ 1
  A_nonneg     : 0 ≤ P.A
  r0_pos       : 0 < P.r0
  p_pos        : 0 < P.p

def w_t_with (cfg : Config) (P : Params) (Tdyn τ0 : ℝ) : ℝ :=
  let t := max cfg.eps_t (Tdyn / τ0)
  1 + P.Clag * (Real.rpow t P.alpha - 1)

@[simp] def w_t (P : Params) (Tdyn τ0 : ℝ) : ℝ := w_t_with defaultConfig P Tdyn τ0

@[simp] def w_t_display (P : Params) (B : BridgeData) (Tdyn : ℝ) : ℝ :=
  w_t_with defaultConfig P Tdyn B.tau0

lemma eps_t_le_one_default : defaultConfig.eps_t ≤ (1 : ℝ) := by
  norm_num

/-- Reference identity under nonzero tick: w_t(τ0, τ0) = 1. -/
lemma w_t_ref_with (cfg : Config) (hcfg : ConfigProps cfg)
  (P : Params) (τ0 : ℝ) (hτ : τ0 ≠ 0) : w_t_with cfg P τ0 τ0 = 1 := by
  dsimp [w_t_with]
  have hdiv : τ0 / τ0 = (1 : ℝ) := by
    field_simp [hτ]
  have hmax : max cfg.eps_t (τ0 / τ0) = (1 : ℝ) := by
    simpa [hdiv, max_eq_right hcfg.eps_t_le_one]
  simp [hmax]

lemma w_t_ref (P : Params) (τ0 : ℝ) (hτ : τ0 ≠ 0) : w_t P τ0 τ0 = 1 :=
  w_t_ref_with defaultConfig defaultConfig_props P τ0 hτ

lemma w_t_rescale_with (cfg : Config) (P : Params) (c Tdyn τ0 : ℝ) (hc : 0 < c) :
  w_t_with cfg P (c * Tdyn) (c * τ0) = w_t_with cfg P Tdyn τ0 := by
  dsimp [w_t_with]
  have hc0 : (c : ℝ) ≠ 0 := ne_of_gt hc
  have : (c * Tdyn) / (c * τ0) = Tdyn / τ0 := by field_simp [hc0]
  simp [this]

lemma w_t_rescale (P : Params) (c Tdyn τ0 : ℝ) (hc : 0 < c) :
  w_t P (c * Tdyn) (c * τ0) = w_t P Tdyn τ0 :=
  w_t_rescale_with defaultConfig P c Tdyn τ0 hc

/-- Nonnegativity of time-kernel under ParamProps. -/
lemma w_t_nonneg_with (cfg : Config) (P : Params) (H : ParamProps P) (Tdyn τ0 : ℝ) :
  0 ≤ w_t_with cfg P Tdyn τ0 := by
  dsimp [w_t_with]
  set t := max cfg.eps_t (Tdyn / τ0) with ht
  have ht_nonneg : 0 ≤ t := by
    have hε : 0 ≤ cfg.eps_t := by
      have : 0 ≤ max cfg.eps_t (Tdyn / τ0) := by
        have := le_max_left cfg.eps_t (Tdyn / τ0); exact le_trans (le_of_lt_or_eq (le_total 0 _) ) this
      exact le_trans (le_max_left _ _) this
    have : cfg.eps_t ≤ t := by simpa [ht] using le_max_left cfg.eps_t (Tdyn / τ0)
    exact le_trans hε this
  have hrpow_nonneg : 0 ≤ Real.rpow t P.alpha := Real.rpow_nonneg_of_nonneg ht_nonneg _
  have hge : Real.rpow t P.alpha - 1 ≥ -1 := by
    have : (0 : ℝ) ≤ Real.rpow t P.alpha := hrpow_nonneg
    have : -1 ≤ Real.rpow t P.alpha - 1 := by linarith
    simpa [sub_eq_add_neg] using this
  have hClag_nonneg : 0 ≤ P.Clag := H.Clag_nonneg
  have hClag_le_one : P.Clag ≤ 1 := H.Clag_le_one
  have hscale : P.Clag * (Real.rpow t P.alpha - 1) ≥ -1 := by
    have : -1 ≤ Real.rpow t P.alpha - 1 := by
      have : (0 : ℝ) ≤ Real.rpow t P.alpha := hrpow_nonneg; linarith
    have := mul_le_mul_of_nonneg_left this hClag_nonneg
    have hleft : (-1 : ℝ) ≤ P.Clag * (-1) := by
      have : -1 ≤ -P.Clag := by simpa using (neg_le_neg hClag_le_one)
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have : P.Clag * (Real.rpow t P.alpha - 1) ≥ P.Clag * (-1) := by
      have h := this; simpa [sub_eq_add_neg] using h
    exact le_trans hleft this
  have : 0 ≤ 1 + P.Clag * (Real.rpow t P.alpha - 1) := by
    have : -1 ≤ P.Clag * (Real.rpow t P.alpha - 1) := by
      simpa [neg_le] using hscale
    linarith
  simpa [w_t_with, ht, add_comm, add_left_comm, add_assoc] using this

lemma w_t_nonneg (P : Params) (H : ParamProps P) (Tdyn τ0 : ℝ) : 0 ≤ w_t P Tdyn τ0 :=
  w_t_nonneg_with defaultConfig P H Tdyn τ0

end
end ILG
end Gravity
end IndisputableMonolith
