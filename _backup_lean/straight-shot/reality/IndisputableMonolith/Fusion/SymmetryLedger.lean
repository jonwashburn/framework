import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Ethics.ConservationLaw

/-!
# Symmetry Ledger

Symmetry-ledger utilities for fusion pulse shaping. Ratios `r_lm` are
mode-normalized magnitudes (`|a_lm| / a_l^*`), weighted by declared
coefficients and aggregated with the canonical recognition cost `J`.
-/
namespace IndisputableMonolith
namespace Fusion

open scoped BigOperators
open Classical

noncomputable section

-- Use the J-cost function from Cost module
local notation "J" => Cost.Jcost

variable {Mode : Type _} [Fintype Mode] [DecidableEq Mode]

/-- Configuration of weights and nominal ratios for a symmetry ledger. -/
structure LedgerConfig where
  weights : Mode → ℝ
  weights_nonneg : ∀ m, 0 ≤ weights m

/-- Observed ratios with positivity witness (domain of `J`). -/
structure ModeRatios where
  ratio : Mode → ℝ
  ratio_pos : ∀ m, 0 < ratio m

namespace ModeRatios

@[simp] lemma ratio_pos' (r : ModeRatios) (m : Mode) : 0 < r.ratio m :=
  r.ratio_pos m

def ofPositive (f : Mode → ℝ) (hf : ∀ m, 0 < f m) : ModeRatios (Mode := Mode) :=
  ⟨f, hf⟩

@[simp] lemma ratio_ofPositive (f : Mode → ℝ) (hf : ∀ m, 0 < f m) :
    (ofPositive (Mode := Mode) f hf).ratio = f := rfl

def isUnity (r : ModeRatios (Mode := Mode)) : Prop :=
  ∀ m, r.ratio m = 1

end ModeRatios

/-- Evaluate the symmetry ledger for a snapshot of ratios. -/
def ledger (cfg : LedgerConfig (Mode := Mode)) (r : ModeRatios (Mode := Mode)) : ℝ :=
  ∑ m, cfg.weights m * J (r.ratio m)

lemma ledger_nonneg (cfg : LedgerConfig (Mode := Mode))
    (r : ModeRatios (Mode := Mode)) :
    0 ≤ ledger cfg r := by
  classical
  refine Finset.sum_nonneg ?term
  intro m hm
  have hJ := Cost.Jcost_nonneg (r.ratio_pos m)
  exact mul_nonneg (cfg.weights_nonneg m) hJ

lemma ledger_eq_zero_of_unity (cfg : LedgerConfig (Mode := Mode))
    (r : ModeRatios (Mode := Mode))
    (hunity : r.isUnity) : ledger cfg r = 0 := by
  classical
  have hJzero : ∀ m, J (r.ratio m) = 0 := by
    intro m
    have := hunity m
    simpa [this] using Cost.Jcost_unit0
  have hterm : ∀ m, cfg.weights m * J (r.ratio m) = 0 := by
    intro m
    simpa [hJzero m]
  have : ∑ m, cfg.weights m * J (r.ratio m) = 0 :=
    Finset.sum_eq_zero fun m _ => hterm m
  simpa [ledger] using this

/-- Per-mode upper bounds (e.g. certificate tolerances). -/
structure ModeThresholds where
  upper : Mode → ℝ
  upper_nonneg : ∀ m, 0 ≤ upper m

def withinThresholds (bounds : ModeThresholds (Mode := Mode))
    (r : ModeRatios (Mode := Mode)) : Prop :=
  ∀ m, r.ratio m ≤ bounds.upper m

lemma unity_within_thresholds (bounds : ModeThresholds (Mode := Mode))
    (r : ModeRatios (Mode := Mode)) (hunity : r.isUnity) :
    withinThresholds bounds r ↔ ∀ m, 1 ≤ bounds.upper m := by
  constructor
  · intro h
    intro m
    have := h m
    simpa [hunity m]
  · intro h m
    have := h m
    simpa [hunity m]

def pass (cfg : LedgerConfig (Mode := Mode))
    (bounds : ModeThresholds (Mode := Mode)) (Λ : ℝ)
    (r : ModeRatios (Mode := Mode)) : Prop :=
  ledger cfg r ≤ Λ ∧ withinThresholds bounds r

lemma unity_pass (cfg : LedgerConfig (Mode := Mode))
    (bounds : ModeThresholds (Mode := Mode)) (Λ : ℝ)
    (r : ModeRatios (Mode := Mode)) (hunity : r.isUnity)
    (hΛ : 0 ≤ Λ) (hbound : ∀ m, 1 ≤ bounds.upper m) :
    pass cfg bounds Λ r := by
  refine And.intro ?ledger ?bounds
  · have hledger := ledger_eq_zero_of_unity (cfg := cfg) (r := r) hunity
    simpa [hledger] using hΛ
  · intro m
    have := hbound m
    simpa [hunity m] using this

end

end Fusion
end IndisputableMonolith
