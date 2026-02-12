/-!
Minimal documentation-side scaffold to record a non-tautological "no alias"
property for a tiny set of documentation entries. Provides a concrete
predicate and a builder with proof. No axioms; no `sorry`.
-/

namespace YM.Docs.NoAlias

/-- A tiny documentation entry with an optional alias target. -/
structure DocEntry where
  id    : Nat
  alias : Option Nat

/-- A small collection of documentation entries. -/
structure DocSet where
  entries : List DocEntry

/-- Concrete no-alias predicate: every entry has no alias set. -/
def noAlias (S : DocSet) : Prop :=
  ∀ e ∈ S.entries, e.alias = none

/-- Minimal builder: empty set of entries which trivially satisfies `noAlias`. -/
def build_docset_noalias : DocSet :=
  { entries := [] }

theorem build_docset_noalias_satisfies : noAlias build_docset_noalias := by
  intro e hmem
  cases hmem

end YM.Docs.NoAlias


