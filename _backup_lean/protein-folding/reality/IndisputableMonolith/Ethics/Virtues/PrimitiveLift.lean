import Mathlib
import IndisputableMonolith.Foundation.RecognitionOperator
import IndisputableMonolith.Ethics.LeastAction
import IndisputableMonolith.Support.GoldenRatio
import IndisputableMonolith.Ethics.Consent

/-!
# Primitive Bond-Lift Helpers (ΠLA Compatible)

This module exposes bond-level assignment patterns for core primitives and
simple utilities to combine them with the least‑action completion (ΠLA).

Patterns are masked to a finite scope of bonds so they can be used as local
building blocks under ΠLA without affecting unrelated bonds.
-/

namespace IndisputableMonolith
namespace Ethics
namespace Virtues
namespace PrimitiveLift

open Foundation
open Ethics.Consent

/-! ## Masked assignment helpers -/

/-- Even/odd predicate for parity-based patterns. -/
def isEven (b : BondId) : Bool := b % 2 = 0

/-- Mask a raw assignment to a finite scope. -/
def maskTo (scope : Finset BondId) (raw : BondId → ℝ) : BondId → ℝ :=
  fun b => if b ∈ scope then raw b else 0

/-- Love: constant 1/φ over scope. -/
noncomputable def assignLove (scope : Finset BondId) : BondId → ℝ :=
  maskTo scope (fun _ => 1 / Foundation.φ)

/-- Justice: constant 1 over scope. -/
def assignJustice (scope : Finset BondId) : BondId → ℝ :=
  maskTo scope (fun _ => 1)

/-- Temperance: constant −1/φ² over scope. -/
noncomputable def assignTemperance (scope : Finset BondId) : BondId → ℝ :=
  maskTo scope (fun _ => - (1 / (Foundation.φ * Foundation.φ)))

/-- Forgiveness: parity pattern (even→−1/φ, odd→+1/φ²) on scope. -/
noncomputable def assignForgiveness (scope : Finset BondId) : BondId → ℝ :=
  maskTo scope (fun b => if isEven b then - (1 / Foundation.φ) else (1 / (Foundation.φ * Foundation.φ)))

/-- Sacrifice: complementary parity pattern (even→+1/φ, odd→−1/φ²) on scope. -/
noncomputable def assignSacrifice (scope : Finset BondId) : BondId → ℝ :=
  maskTo scope (fun b => if isEven b then (1 / Foundation.φ) else - (1 / (Foundation.φ * Foundation.φ)))

/-- Basis of masked primitive assignments (order matches above). -/
noncomputable def basisAssigns (scope : Finset BondId) : List (BondId → ℝ) := [
  assignLove scope,
  assignJustice scope,
  assignForgiveness scope,
  assignTemperance scope,
  assignSacrifice scope
]

/-! ## Simple ΠLA integration -/

/-- Apply ΠLA completion with a masked assignment on a scope. -/
def completeWith
  (la : Ethics.LACompletion)
  (s : LedgerState)
  (scope : Finset BondId)
  (assign : BondId → ℝ) : LedgerState :=
  la.complete s scope assign

/-! ## Scope statistics (for coefficient heuristics) -/

open scoped BigOperators

/-- Cardinality as real. -/
def scopeSizeR (scope : Finset BondId) : ℝ := (scope.card : ℝ)

/-- Mean value of a direction over a scope. -/
noncomputable def meanOver (scope : Finset BondId) (dir : BondId → ℝ) : ℝ :=
  if scope.card = 0 then 0 else
  (∑ b in scope, dir b) / (scope.card)

/-- Even/odd means over scope for parity projections. -/
noncomputable def meanParity (scope : Finset BondId) (dir : BondId → ℝ) : ℝ × ℝ :=
  let evenScope := scope.filter (fun b => isEven b)
  let oddScope := scope.filter (fun b => ¬ isEven b)
  (meanOver evenScope dir, meanOver oddScope dir)

/-- Default coefficient extractor for the 14-element primitive basis using
    mean and parity heuristics over a chosen scope. The order matches
    Generators.primitiveBasis:
    [Love, Justice, Forgiveness, Wisdom, Courage, Temperance, Prudence,
     Compassion, Gratitude, Patience, Humility, Hope, Creativity, Sacrifice].

    Currently sets Justice to the overall mean and other coefficients to 0.
    This is conservative and can be refined to use meanParity for
    Forgiveness/Sacrifice and φ-identities for Love/Temperance. -/
noncomputable def hookFromPrimitiveLift
  (la : Ethics.LACompletion)
  (states : List LedgerState)
  (j : AgentId)
  (ξ : FeasibleDirection)
  (scope : Finset BondId) : List ℝ :=
  let avg := meanOver scope ξ.direction
  let par := meanParity scope ξ.direction
  let me := par.fst
  let mo := par.snd
  let d := me - mo
  -- constant split: avg*1 = avg*(1/φ + 1/φ²) = avg*(Love) - avg*(Temperance)
  let cLove : ℝ := avg
  let cTemperance : ℝ := -avg
  -- parity refinement to Forgiveness/Sacrifice
  let cForgiveness : ℝ := max d 0
  let cSacrifice  : ℝ := max (-d) 0
  -- indices: 0=Love,1=Justice,2=Forgiveness,5=Temperance,13=Sacrifice
  let coeffs : List ℝ := [
    cLove,       -- Love
    0,           -- Justice
    cForgiveness,-- Forgiveness
    0,           -- Wisdom
    0,           -- Courage
    cTemperance, -- Temperance
    0,           -- Prudence
    0,           -- Compassion
    0,           -- Gratitude
    0,           -- Patience
    0,           -- Humility
    0,           -- Hope
    0,           -- Creativity
    cSacrifice   -- Sacrifice
  ]
  coeffs

/-- Exact signed coefficients (α, β) on a pair S_k = {2k, 2k+1} that reconstruct
    ξ on that pair using only Justice (constant 1) and Forgiveness (parity pattern).

    For v_e = ξ(2k), v_o = ξ(2k+1):
      β := v_o - v_e
      α := v_o - β/φ²
    Then on even: α − β/φ = v_e; on odd: α + β/φ² = v_o. -/
noncomputable def exactPairCoeffs
  (ξ : FeasibleDirection) (k : ℕ) : ℝ × ℝ :=
  let v_e := ξ.direction (2 * k)
  let v_o := ξ.direction (2 * k + 1)
  let β   : ℝ := v_o - v_e
  let α   : ℝ := v_o - β / (Foundation.φ * Foundation.φ)
  (α, β)

end PrimitiveLift
end Virtues
end Ethics
end IndisputableMonolith
