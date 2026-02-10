import Mathlib
import IndisputableMonolith.Verification.Necessity.LedgerNecessity

/-!
Constructive well-foundedness of evolution from a tick labelling.

We expose a minimal interface `HasTick` that asserts the existence of a
strictly increasing natural-number tick along evolution edges. From this we
derive that the reversed evolution relation is well-founded and that 2-cycles
are impossible. These lemmas can be used to replace ad-hoc well-foundedness
assumptions by a tick-oriented derivation.
-/

namespace IndisputableMonolith
namespace Foundation
namespace EvolutionWellFounded

open Nat

namespace VN := IndisputableMonolith.Verification.Necessity.LedgerNecessity

/-- If ticks strictly increase along evolution, then the reversed evolution
    relation is well-founded (no infinite backward chains). -/
theorem evolution_wf_from_ticks
  {E : VN.DiscreteEventSystem}
  {ev : VN.EventEvolution E}
  (h : VN.HasTick E ev)
  : WellFounded (fun a b : E.Event => ev.evolves b a) := by
  -- Consider the measure relation Rₘ a b : tick b < tick a
  let Rm : E.Event → E.Event → Prop := fun a b => h.tick b < h.tick a
  -- R (reversed evolution) is a subrelation of the measure relation
  have subR : ∀ {a b}, (ev.evolves b a) → Rm a b := by
    intro a b hba; exact h.mono hba
  -- Rm is well-founded by strong induction on tick(a)
  have wfRm : WellFounded Rm := by
    refine ⟨?_⟩
    -- Acc for any `a` by induction on n = tick a
    have acc_of_le : ∀ n : Nat, ∀ a : E.Event, h.tick a ≤ n → Acc Rm a := by
      intro n; induction' n with n ih
      · intro a hle
        have h0 : h.tick a = 0 := Nat.le_zero.mp hle
        refine Acc.intro a ?step
        intro b hb
        have : h.tick b < 0 := by simpa [h0] using hb
        exact (Nat.not_lt_zero _ this).elim
      · intro a hle
        refine Acc.intro a ?step
        intro b hb
        have hb_lt_succ : h.tick b < n.succ := lt_of_lt_of_le hb hle
        have hb_le_n : h.tick b ≤ n := Nat.lt_succ_iff.mp hb_lt_succ
        exact ih b hb_le_n
    intro a
    exact acc_of_le (h.tick a) a (le_rfl)
  -- Subrelation preserves well-foundedness
  exact WellFounded.subrelation subR wfRm

/-- No 2-cycles under strictly increasing ticks. -/
theorem no_two_cycle_from_ticks
  {E : VN.DiscreteEventSystem}
  {ev : VN.EventEvolution E}
  (h : VN.HasTick E ev)
  : ∀ a b : E.Event, ev.evolves a b → ev.evolves b a → False := by
  intro a b hab hba
  have h1 : h.tick a < h.tick b := h.mono hab
  have h2 : h.tick b < h.tick a := h.mono hba
  exact lt_irrefl _ (lt_trans h1 h2)

end EvolutionWellFounded
end Foundation
end IndisputableMonolith
