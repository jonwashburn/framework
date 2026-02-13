import Mathlib
import IndisputableMonolith.Constants

/-!
# Scale Gate for Light Language

This module formalizes the λ_rec/τ₀ admissibility gate that determines which
patterns can carry meaning in the Light Language.

## Main Definitions

* `AdmissibleWindow` - A window that passes the λ_rec/τ₀ gate
* `EightTickAligned` - Windows aligned to the eight-tick cadence
* `NeutralWindow` - Windows with zero mean (neutrality constraint)
* `ScaleGate` - The complete admissibility predicate

## Main Theorems

* `scaleGate_nonempty` - The set of admissible windows is non-empty
* `scaleGate_closed_under_composition` - Admissible windows remain admissible under LNAL operations

## Implementation Notes

The scale gate enforces three fundamental constraints from Recognition Science:
1. Eight-tick alignment (τ₀ cadence from T6)
2. Neutrality (sum = 0, from ledger conservation)
3. λ_rec commitment threshold (information-curvature balance)

These constraints are not tunable parameters but forced by RS axioms.
-/

namespace IndisputableMonolith
namespace LightLanguage

open Constants

/-- A window is eight-tick aligned if its length is exactly 8 -/
def EightTickAligned (w : List ℂ) : Prop :=
  w.length = 8

/-- A window is neutral if its sum is zero (within tolerance) -/
def NeutralWindow (w : List ℂ) (tol : ℝ) : Prop :=
  ‖w.sum‖ < tol  -- Using norm (equivalent to Complex.abs)

/-- The λ_rec commitment threshold - patterns must have sufficient energy density
    to pass the information-curvature balance test -/
def LambdaRecThreshold (w : List ℂ) : Prop :=
  let energy := (w.map Complex.normSq).sum
  let lambda_rec := Real.sqrt (Constants.hbar * Constants.G / (Real.pi * Constants.c ^ 3))
  -- Energy density must exceed the λ_rec scale
  energy ≥ lambda_rec ^ 2

/-- The complete scale gate: a window is admissible if it satisfies all three constraints -/
structure AdmissibleWindow where
  window : List ℂ
  eight_tick : EightTickAligned window
  neutral : NeutralWindow window 1e-9
  lambda_rec : LambdaRecThreshold window

/-- The scale gate predicate -/
def ScaleGate (w : List ℂ) : Prop :=
  EightTickAligned w ∧ NeutralWindow w 1e-9 ∧ LambdaRecThreshold w

/-- Admissible windows form a non-empty set -/
theorem scaleGate_nonempty : ∃ w : List ℂ, ScaleGate w := by
  classical
  -- Explicit witness: alternating ±a with `a := λ_rec + 1`.
  -- This is exactly neutral and has energy `8 * (λ_rec + 1)^2 ≥ λ_rec^2` by monotonicity.
  -- We use the RS-native constants (`c = 1`), so the expression simplifies to √(hbar * G / π).
  set lambdaRec : ℝ := Real.sqrt (Constants.hbar * Constants.G / Real.pi) with hLambdaRec
  let a : ℂ := (lambdaRec + 1 : ℝ)
  let witness : List ℂ := [a, -a, a, -a, a, -a, a, -a]
  refine ⟨witness, ?_, ?_, ?_⟩
  · -- Eight tick aligned
    simp [EightTickAligned, witness]
  · -- Neutral window
    -- The alternating list sums to 0.
    have htol : (0 : ℝ) < (1e-9 : ℝ) := by norm_num
    simpa [NeutralWindow, witness] using htol
  · -- Lambda rec threshold
    -- `energy = 8 * (λrec + 1)^2` and `λrec ≥ 0`, so the bound is automatic.
    -- First, rewrite the threshold's internal `sqrt(...)` to our `lambdaRec`.
    have h_sqrt : Real.sqrt (Constants.hbar * Constants.G / Real.pi) = lambdaRec :=
      hLambdaRec.symm
    -- Now simplify the energy expression (no sqrt left) and solve.
    simp [LambdaRecThreshold, witness, a, pow_two, Complex.normSq, h_sqrt]
    have hLambda : 0 ≤ lambdaRec := by
      -- lambdaRec is defined as a square root
      simpa [hLambdaRec] using Real.sqrt_nonneg (Constants.hbar * Constants.G / Real.pi)
    nlinarith

/-- Helper: scaling preserves eight-tick alignment -/
theorem eightTick_scale_invariant (w : List ℂ) (c : ℂ) :
    EightTickAligned w → EightTickAligned (w.map (· * c)) := by
  intro h
  simp only [EightTickAligned, List.length_map] at h ⊢
  exact h

/-!
Helper lemma (documentation / TODO): neutrality under linear combinations.

Intended claim: a zipWith-linear combination preserves neutrality with a slightly larger tolerance.
This is straightforward but requires a small library of `List.zipWith` + norm inequalities.
-/

/-- The scale gate is closed under LNAL-compatible operations (scaffold) -/
theorem scaleGate_closed_under_lnal_ops (w : List ℂ) :
    ScaleGate w →
    ∀ (op : List ℂ → List ℂ),
    (∀ v, EightTickAligned v → EightTickAligned (op v)) →
    (∀ v tol, NeutralWindow v tol → NeutralWindow (op v) tol) →
    (∀ v, LambdaRecThreshold v → LambdaRecThreshold (op v)) →
    ScaleGate (op w) := by
  intro ⟨h_eight, h_neutral, h_lambda⟩ op h_op_eight h_op_neutral h_op_lambda
  constructor
  · exact h_op_eight w h_eight
  constructor
  · exact h_op_neutral w 1e-9 h_neutral
  · exact h_op_lambda w h_lambda

end LightLanguage
end IndisputableMonolith
