import Mathlib
import IndisputableMonolith.Verification.Necessity.LedgerNecessity

/-!
# Ledger Horizon: finite active region at finite tick

This module formalizes the “both can be true” resolution:

- The **global carrier** (voxel-space / event-space) may be infinite or compact.
- But under **local finiteness** (finite neighbors per node), the **region reachable
  in a finite number of steps** from a finite seed is **finite**.

This is the precise, model-independent way to encode:

> “There is no observed boundary because only a finite region is active/accessible
>  at any finite tick.”

It intentionally does **not** decide global topology (ℤ³ vs compact quotient); that
requires extra global assumptions beyond local finiteness.
-/

noncomputable section
open Classical

namespace IndisputableMonolith
namespace Verification
namespace Necessity

namespace LedgerHorizon

open LedgerNecessity

variable {E : DiscreteEventSystem} (ev : EventEvolution E) [LocalFinite E ev]

/-- One-step expansion along the relation `ev.evolves`. -/
def step (S : Set E.Event) : Set E.Event :=
  {v | ∃ e, e ∈ S ∧ ev.evolves e v}

private lemma finite_step {S : Set E.Event} (hS : S.Finite) :
    (step ev S).Finite := by
  classical
  -- Induct on the finite seed set.
  refine Set.Finite.induction_on
    (s := S) (hs := hS)
    (motive := fun s _ => (step ev s).Finite) ?h0 ?hins
  · -- empty seed set expands to empty
    simp [step]
  · intro a S haS hSfin ih
    -- Expand (insert a S) = out(a) ∪ expand(S)
    have hdecomp :
        step ev (insert a S) =
          ({v | ev.evolves a v} ∪ step ev S) := by
      ext v
      constructor
      · intro hv
        rcases hv with ⟨e, he, hev⟩
        rcases he with rfl | heS
        · exact Or.inl hev
        · exact Or.inr ⟨e, heS, hev⟩
      · intro hv
        cases hv with
        | inl hev =>
            exact ⟨a, Or.inl rfl, hev⟩
        | inr hvS =>
            rcases hvS with ⟨e, heS, hev⟩
            exact ⟨e, Or.inr heS, hev⟩
    -- Each one-step out-neighborhood is finite by LocalFinite.
    have hout : ({v : E.Event | ev.evolves a v} : Set E.Event).Finite := by
      -- `Precedence` is an alias of `ev.evolves`.
      simpa [LedgerNecessity.Precedence] using
        (LedgerNecessity.Precedence.finite_out (ev := ev) a)
    -- Union of two finite sets is finite.
    rw [hdecomp]
    exact hout.union ih

/-- The exact-n frontier from a single seed `e0` under repeated `step`. -/
def frontier (e0 : E.Event) : Nat → Set E.Event
  | 0 => {e0}
  | Nat.succ n => step ev (frontier e0 n)

/-- The ≤n “ball” from a seed `e0`: union of frontiers up to n. -/
def ball (e0 : E.Event) : Nat → Set E.Event
  | 0 => frontier (ev := ev) e0 0
  | Nat.succ n => ball e0 n ∪ frontier (ev := ev) e0 (Nat.succ n)

theorem finite_frontier (e0 : E.Event) :
    ∀ n : Nat, (frontier (ev := ev) e0 n).Finite := by
  intro n
  induction n with
  | zero =>
      simpa [frontier] using (Set.finite_singleton e0)
  | succ n ih =>
      -- one more step preserves finiteness
      simpa [frontier] using (finite_step (ev := ev) ih)

theorem finite_ball (e0 : E.Event) :
    ∀ n : Nat, (ball (ev := ev) e0 n).Finite := by
  intro n
  induction n with
  | zero =>
      simpa [ball, frontier] using (Set.finite_singleton e0)
  | succ n ih =>
      have hf : (frontier (ev := ev) e0 (Nat.succ n)).Finite :=
        finite_frontier (ev := ev) e0 (Nat.succ n)
      simpa [ball] using (ih.union hf)

end LedgerHorizon

end Necessity
end Verification
end IndisputableMonolith
