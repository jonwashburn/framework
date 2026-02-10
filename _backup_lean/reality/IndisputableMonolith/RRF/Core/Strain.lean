import Mathlib.Data.Real.Basic
import Mathlib.Order.Basic


/-!
# RRF Core: Strain

Strain is the fundamental measure of "how far from equilibrium/balance" a state is.

In RRF:
- Strain → 0 is the law (J → 0)
- Strain encodes deviation from recognition/balance
- Lower strain = more consistent = more "real"

This module provides the abstract interface for strain functionals.
-/

namespace IndisputableMonolith
namespace RRF.Core

/-- A strain functional on a state space.

A strain functional assigns a non-negative cost to each state.
The key property: `J(x) = 0` iff `x` is at equilibrium/balanced.

We use `ℝ` as the codomain and add nonnegativity as a class constraint.
-/
structure StrainFunctional (State : Type*) where
  /-- The strain/cost of a state. -/
  J : State → ℝ

namespace StrainFunctional

variable {State : Type*}

/-- A strain functional is non-negative if J(x) ≥ 0 for all x. -/
class NonNeg (S : StrainFunctional State) : Prop where
  nonneg : ∀ x, 0 ≤ S.J x

/-- A state is balanced/equilibrium if its strain is exactly zero. -/
def isBalanced (S : StrainFunctional State) (x : State) : Prop :=
  S.J x = 0

/-- The set of equilibrium states. -/
def equilibria (S : StrainFunctional State) : Set State :=
  { x | S.isBalanced x }

/-- A strain functional has a unique minimum if there's exactly one equilibrium. -/
def hasUniqueMin (S : StrainFunctional State) : Prop :=
  ∃! x, S.isBalanced x

/-- Strict improvement: x is strictly better than y. -/
def strictlyBetter (S : StrainFunctional State) (x y : State) : Prop :=
  S.J x < S.J y

/-- Weak improvement: x is at least as good as y. -/
def weaklyBetter (S : StrainFunctional State) (x y : State) : Prop :=
  S.J x ≤ S.J y

/-- A state x is a minimizer if no state is strictly better. -/
def isMinimizer (S : StrainFunctional State) (x : State) : Prop :=
  ∀ y, S.weaklyBetter x y

/-- For non-negative strain, equilibria are minimizers. -/
theorem equilibria_are_minimizers [NonNeg S] (x : State) (hx : S.isBalanced x) :
    S.isMinimizer x := by
  intro y
  simp only [weaklyBetter, isBalanced] at *
  rw [hx]
  exact NonNeg.nonneg y

end StrainFunctional

/-- A ledger constraint: the sum of debits equals the sum of credits. -/
structure LedgerConstraint (State : Type*) where
  /-- Total debit for a state. -/
  debit : State → ℤ
  /-- Total credit for a state. -/
  credit : State → ℤ

namespace LedgerConstraint

variable {State : Type*}

/-- A state satisfies the ledger constraint if debit = credit. -/
def isClosed (L : LedgerConstraint State) (x : State) : Prop :=
  L.debit x = L.credit x

/-- The net balance (should be zero for closed ledgers). -/
def net (L : LedgerConstraint State) (x : State) : ℤ :=
  L.debit x - L.credit x

theorem closed_iff_net_zero (L : LedgerConstraint State) (x : State) :
    L.isClosed x ↔ L.net x = 0 := by
  simp [isClosed, net, sub_eq_zero]

end LedgerConstraint

/-- Combined strain and ledger: the full RRF state evaluation. -/
structure StrainLedger (State : Type*) where
  strain : StrainFunctional State
  ledger : LedgerConstraint State

namespace StrainLedger

variable {State : Type*}

/-- A state is valid if it has zero strain and closed ledger. -/
def isValid (SL : StrainLedger State) (x : State) : Prop :=
  SL.strain.isBalanced x ∧ SL.ledger.isClosed x

/-- The set of valid states. -/
def validStates (SL : StrainLedger State) : Set State :=
  { x | SL.isValid x }

end StrainLedger

end RRF.Core
end IndisputableMonolith
