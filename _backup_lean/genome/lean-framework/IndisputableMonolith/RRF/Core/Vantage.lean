import Mathlib.Data.Fintype.Card


/-!
# RRF Core: Vantage

The three fundamental perspectives on the One Thing.

In RRF, every phenomenon can be viewed from three vantages:
- **Inside**: The subjective/qualia view (what it feels like)
- **Act**: The dynamic/process view (what is happening)
- **Outside**: The objective/physics view (what is observed)

These are not three different things, but three views of the same thing.
The key insight: all three must be consistent for existence to be actual.
-/

namespace IndisputableMonolith
namespace RRF.Core

/-- The three fundamental vantages on reality.

- `inside`: The subjective perspective (qualia, meaning, experience)
- `act`: The dynamic perspective (recognition, process, becoming)
- `outside`: The objective perspective (physics, measurement, observation)
-/
inductive Vantage : Type where
  | inside : Vantage
  | act : Vantage
  | outside : Vantage
  deriving DecidableEq, Repr, Inhabited

namespace Vantage

/-- Vantage is finite with exactly 3 elements. -/
instance : Fintype Vantage where
  elems := ⟨[inside, act, outside], by decide⟩
  complete := fun v => by cases v <;> decide

/-- The number of vantages. -/
theorem card_vantage : Fintype.card Vantage = 3 := rfl

/-- Every vantage has a complement pair. -/
def complements (v : Vantage) : Vantage × Vantage :=
  match v with
  | inside  => (act, outside)
  | act     => (inside, outside)
  | outside => (inside, act)

/-- Cyclic successor (for the 3-phase rhythm). -/
def succ (v : Vantage) : Vantage :=
  match v with
  | inside  => act
  | act     => outside
  | outside => inside

/-- Cyclic predecessor. -/
def pred (v : Vantage) : Vantage :=
  match v with
  | inside  => outside
  | act     => inside
  | outside => act

theorem succ_pred_id (v : Vantage) : succ (pred v) = v := by
  cases v <;> rfl

theorem pred_succ_id (v : Vantage) : pred (succ v) = v := by
  cases v <;> rfl

/-- Three applications of succ returns to start. -/
theorem succ_succ_succ (v : Vantage) : succ (succ (succ v)) = v := by
  cases v <;> rfl

end Vantage

/-- A triple of values indexed by vantage.
    Used to express that X_inside, X_act, X_outside are the same underlying X. -/
structure VantageTriple (α : Type*) where
  inside  : α
  act     : α
  outside : α

namespace VantageTriple

/-- Project a value by vantage. -/
def get {α : Type*} (t : VantageTriple α) (v : Vantage) : α :=
  match v with
  | Vantage.inside  => t.inside
  | Vantage.act     => t.act
  | Vantage.outside => t.outside

/-- A unified triple: all three vantages see the same value. -/
def unified {α : Type*} (x : α) : VantageTriple α :=
  { inside := x, act := x, outside := x }

/-- Predicate: the triple is unified (all equal). -/
def isUnified {α : Type*} [DecidableEq α] (t : VantageTriple α) : Prop :=
  t.inside = t.act ∧ t.act = t.outside

theorem unified_is_unified {α : Type*} [DecidableEq α] (x : α) :
    isUnified (unified x) := ⟨rfl, rfl⟩

end VantageTriple

end RRF.Core
end IndisputableMonolith
