import Mathlib
import IndisputableMonolith.LightLanguage.Basis.DFT8
import IndisputableMonolith.ProteinFolding.Basic.EightBeatCycle

/-!
# Phase 1: Neutrality from Ledger Conservation

This module proves that ledger conservation (double-entry balance) forces
the DC component of the DFT-8 decomposition to vanish.

## The Derivation

1. A `ValidLedgerWindow` has its costs summed to zero (Ledger Conservation).
2. The DC coefficient of an 8-tick DFT is proportional to the sum of the entries.
3. Therefore, a balanced ledger window has exactly zero DC component.
-/

namespace IndisputableMonolith.LightLanguage

open Basis
open ProteinFolding.EightBeatCycle

/-- The DC coefficient of a 8-vector is proportional to its sum. -/
lemma dft8_dc_coeff_proportional_to_sum (v : Fin 8 → ℂ) :
    (Finset.univ.sum (fun t => star (dft8_mode 0 t) * v t)) =
    (1 / Real.sqrt 8) * (Finset.univ.sum v) := by
  -- Mode 0 is constant 1/√8
  have h_mode : ∀ t, dft8_mode 0 t = 1 / Real.sqrt 8 := dft8_mode_zero_constant
  simp only [h_mode, star_div₀, Complex.star_def, Complex.conj_ofReal, star_one]
  rw [← Finset.mul_sum]

/-- **Phase 1 Derivation**: Ledger balance forces DC coefficient to vanish. -/
theorem ledger_balance_implies_DC_zero (L : ValidLedgerWindow) :
    (Finset.univ.sum (fun t => star (dft8_mode 0 t) * (L.costs t : ℂ))) = 0 := by
  -- 1. Get the ledger balance property
  have h_bal : (∑ k : Beat, L.costs k) = 0 := L.balanced

  -- 2. Use the proportionality lemma
  rw [dft8_dc_coeff_proportional_to_sum]

  -- 3. Substitute the balanced sum
  have h_sum_zero : (∑ t : Fin 8, (L.costs t : ℂ)) = 0 := by
    rw [← Complex.ofReal_sum]
    simp [h_bal]

  rw [h_sum_zero]
  simp

/-- **Phase 1 Certificate**: Neutrality from Ledger. -/
structure NeutralityFromLedgerCert where
  deriving Repr

@[simp] def NeutralityFromLedgerCert.verified (_c : NeutralityFromLedgerCert) : Prop :=
  ∀ L : ValidLedgerWindow, (Finset.univ.sum (fun t => star (dft8_mode 0 t) * (L.costs t : ℂ))) = 0

@[simp] theorem NeutralityFromLedgerCert.verified_any (c : NeutralityFromLedgerCert) :
    NeutralityFromLedgerCert.verified c := by
  intro L
  exact ledger_balance_implies_DC_zero L

/-- Neutrality constraint (σ = 0) is satisfied by any balanced ledger window. -/
theorem ledger_conservation_satisfies_neutrality (L : ValidLedgerWindow) :
    (Finset.univ.sum (fun t => (L.costs t : ℂ)) = 0) := by
  rw [← Complex.ofReal_sum]
  simp [L.balanced]

end IndisputableMonolith.LightLanguage
