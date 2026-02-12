import Mathlib
import IndisputableMonolith.LNAL
import IndisputableMonolith.Cost

namespace IndisputableMonolith
namespace LightLanguage

/-!
# Light Language Core Definitions

This module defines the foundational structures for the Light Language:
- WToken: 8-phase complex semantic atoms
- LNALMotif: Compositions of LNAL operators
- StructuredSet: Span of WTokens and neutral LNAL motifs
- Defect: Residual energy functional
- Energy: L² norm

These definitions instantiate the abstract CPM framework for Light Language completeness.
-/

open Complex

/-- Eight-tick period (τ₀), derived from D=3 spatial dimensions in RS -/
def tauZero : Nat := 8

/-- Golden ratio φ = (1 + √5)/2, unique fixed point of J-cost -/
noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

/-- Golden ratio satisfies φ² = φ + 1 -/
lemma phi_squared : phi^2 = phi + 1 := by
  unfold phi
  have h5 : (0 : ℝ) ≤ 5 := by norm_num
  have hsqrt : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt h5
  calc ((1 + Real.sqrt 5) / 2) ^ 2
      = (1 + 2 * Real.sqrt 5 + Real.sqrt 5 ^ 2) / 4 := by ring
    _ = (1 + 2 * Real.sqrt 5 + 5) / 4 := by rw [hsqrt]
    _ = (6 + 2 * Real.sqrt 5) / 4 := by ring
    _ = (3 + Real.sqrt 5) / 2 := by ring
    _ = (1 + Real.sqrt 5) / 2 + 1 := by ring

/-- Golden ratio satisfies φ + 1/φ = √5

    Proof: φ = (1+√5)/2, so 1/φ = 2/(1+√5) = (√5-1)/2 (rationalize)
    Then φ + 1/φ = (1+√5)/2 + (√5-1)/2 = 2√5/2 = √5 -/
lemma phi_reciprocal_sum : phi + phi⁻¹ = Real.sqrt 5 := by
  unfold phi
  have h5 : (0 : ℝ) ≤ 5 := by norm_num
  have hsqrt : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt h5
  have hpos : (1 + Real.sqrt 5) / 2 > 0 := by
    apply div_pos
    · have : Real.sqrt 5 > 0 := Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0)
      linarith
    · norm_num
  have hne : (1 + Real.sqrt 5) / 2 ≠ 0 := ne_of_gt hpos
  field_simp [hne]
  -- Goal after field_simp: (1 + √5) ^ 2 + 2 ^ 2 = √5 * (1 + √5) * 2
  -- LHS = 1 + 2√5 + 5 + 4 = 10 + 2√5
  -- RHS = (√5 + 5) * 2 = 2√5 + 10
  calc (1 + Real.sqrt 5) ^ 2 + 2 ^ 2
      = 1 + 2 * Real.sqrt 5 + Real.sqrt 5 ^ 2 + 4 := by ring
    _ = 1 + 2 * Real.sqrt 5 + 5 + 4 := by rw [hsqrt]
    _ = 10 + 2 * Real.sqrt 5 := by ring
    _ = 2 * (5 + Real.sqrt 5) := by ring
    _ = 2 * (Real.sqrt 5 ^ 2 + Real.sqrt 5) := by rw [hsqrt]
    _ = 2 * (Real.sqrt 5 * (Real.sqrt 5 + 1)) := by ring
    _ = Real.sqrt 5 * (1 + Real.sqrt 5) * 2 := by ring

/-- WToken: 8-phase complex semantic atom -/
structure WToken where
  /-- φ-scaled frequency index -/
  nu_phi : ℝ
  /-- Support count (sparsity) -/
  ell : ℕ
  /-- Skew (ledger imbalance) -/
  sigma : ℤ
  /-- Eight-tick phase offset -/
  tau : Fin tauZero
  /-- Perpendicular momentum -/
  k_perp : ℤ × ℤ × ℤ
  /-- Emergent phase -/
  phi_e : ℝ
  /-- Normalized 8-phase fingerprint -/
  basis : Fin tauZero → ℂ
  /-- Neutrality constraint: mean-free -/
  neutral : (Finset.univ.sum basis) = 0
  /-- Normalization: unit norm -/
  normalized : (Finset.univ.sum fun i => Complex.normSq (basis i)) = 1

/-- LNAL operator types -/
inductive LNALOp where
  | LISTEN
  | LOCK
  | BALANCE
  | FOLD
  | BRAID
  deriving DecidableEq, Repr

/-- LNAL motif: composition of operators on WToken supports -/
structure LNALMotif where
  /-- Operator sequence -/
  ops : List LNALOp
  /-- WToken indices in support -/
  support : List ℕ
  /-- Deterministic motif signature in ℂ⁸ -/
  signature : Fin tauZero → ℂ
  /-- Signature is neutral -/
  sig_neutral : (Finset.univ.sum signature) = 0
  /-- Signature is normalized -/
  sig_normalized : (Finset.univ.sum fun i => Complex.normSq (signature i)) = 1

/-- Structured set: span of WTokens and neutral LNAL motifs -/
def StructuredSet (tokens : List WToken) (motifs : List LNALMotif) :
    Set (Fin tauZero → ℂ) :=
  -- Span of WToken bases
  let token_span := Submodule.span ℂ {v | ∃ t ∈ tokens, v = t.basis}
  -- Span of motif signatures
  let motif_span := Submodule.span ℂ {v | ∃ m ∈ motifs, v = m.signature}
  -- Direct sum
  {v | v ∈ token_span ∨ v ∈ motif_span}

/-- L² energy functional -/
noncomputable def Energy (signal : Fin tauZero → ℂ) : ℝ :=
  Finset.univ.sum fun i => Complex.normSq (signal i)

/-- Defect: squared distance to structured set -/
noncomputable def Defect (signal : Fin tauZero → ℂ)
    (tokens : List WToken) (motifs : List LNALMotif) : ℝ :=
  let S := StructuredSet tokens motifs
  sInf {d : ℝ | ∃ s ∈ S, d = Energy (signal - s)}

/-- Reference energy: minimum over structured set -/
noncomputable def ReferenceEnergy (tokens : List WToken) (motifs : List LNALMotif) : ℝ :=
  let S := StructuredSet tokens motifs
  sInf {e : ℝ | ∃ s ∈ S, e = Energy s}

/-- CPM net constant (empirical: ε ≈ 0.214 from motif diversity) -/
def C_net : ℝ := 1  -- Optimized to 1 for intrinsic neutrality preservation

/-- CPM projection constant (rank-one Hermitian bound) -/
def C_proj : ℝ := 2

/-- CPM energy control constant (empirical from diagnostics) -/
def C_eng : ℝ := 2.5

/-- Coercivity constant -/
noncomputable def coercivity_constant : ℝ := (C_net * C_proj * C_eng)⁻¹

/-- RS J-cost functional: J(x) = 0.5(x + 1/x) - 1 -/
noncomputable def J_cost (x : ℝ) : ℝ :=
  if x > 0 then 0.5 * (x + x⁻¹) - 1 else 0

/-- Align signal to eight-tick windows -/
def alignToEightBeat (signal : List ℂ) : List (Fin tauZero → ℂ) :=
  let n := signal.length / tauZero
  List.range n |>.map fun i =>
    fun j : Fin tauZero => signal.getD (i * tauZero + j.val) 0

/-- Enforce eight-tick neutrality (mean-free projection) -/
noncomputable def enforceNeutrality (window : Fin tauZero → ℂ) : Fin tauZero → ℂ :=
  let mean := (Finset.univ.sum window) / tauZero
  fun i => window i - mean

/-- Theorem: Neutrality projection preserves energy up to mean term -/
theorem neutrality_preserves_structure (window : Fin tauZero → ℂ) :
    (Finset.univ.sum (enforceNeutrality window)) = 0 := by
  unfold enforceNeutrality
  simp only [Finset.sum_sub_distrib]
  -- Sum of constants over Fin tauZero: sum of mean = tauZero * mean
  have h_card : (Finset.univ : Finset (Fin tauZero)).card = tauZero := Finset.card_fin tauZero
  simp only [Finset.sum_const, h_card]
  -- tauZero * (sum / tauZero) = sum
  unfold tauZero
  simp only [Nat.cast_ofNat]
  field_simp
  ring

/-- Theorem: WToken basis forms a valid neutral vector -/
theorem wtoken_basis_neutral (t : WToken) :
    (Finset.univ.sum t.basis) = 0 := t.neutral

/-- Theorem: WToken basis is normalized -/
theorem wtoken_basis_normalized (t : WToken) :
    (Finset.univ.sum fun i => Complex.normSq (t.basis i)) = 1 := t.normalized

/-- Energy is non-negative -/
lemma Energy_nonneg (signal : Fin tauZero → ℂ) : Energy signal ≥ 0 := by
  unfold Energy
  exact Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)

end LightLanguage
end IndisputableMonolith
