import Mathlib

/-!
  Atomicity.lean

  Purpose: Tighten T2 by providing a constructive, axiom‑free serialization
  result for finite recognition histories. We work abstractly over an event
  type `E` with a precedence relation `prec` encoding ledger/causal constraints.

  Key outcomes:
  - Existence of a one‑per‑tick (sequential) schedule for any finite history
    that respects `prec` (topological ordering via a deterministic pick‑minimal
    recursion).
  - A generic preservation lemma: if a conservation predicate is preserved by
    single postings, then it is preserved by any sequential schedule over a
    finite history.

  Notes:
  - We deliberately keep this module independent of cost/convexity (T5) and
    only assume finiteness and decidable precedence on the finite history.
  - Proofs are constructive over `Finset`; we avoid adding axioms.
-/

namespace IndisputableMonolith
namespace Foundation

noncomputable section

open scoped BigOperators
open Finset

/-- A precedence relation on events. Read `prec e₁ e₂` as “e₁ must occur before e₂”. -/
abbrev Precedence (E : Type _) := E → E → Prop

namespace Atomicity

variable {E : Type _}

/-- `isMinimalIn prec H e` means `e` is in `H` and has no predecessors in `H`. -/
def isMinimalIn (prec : Precedence E) [DecidableEq E] [DecidableRel prec]
    (H : Finset E) (e : E) : Prop :=
  e ∈ H ∧ ∀ e' ∈ H, ¬ prec e' e

lemma isMinimalIn.mem {prec : Precedence E} [DecidableEq E] [DecidableRel prec]
    {H : Finset E} {e : E} :
    isMinimalIn (E:=E) prec H e → e ∈ H :=
  And.left

/-- Minimality existence on a finite, nonempty `H` under well‑founded precedence. -/
lemma exists_minimal_in
    (prec : Precedence E) [DecidableRel prec] [DecidableEq E]
    (wf : WellFounded prec) {H : Finset E} (hH : H.Nonempty) :
    ∃ e ∈ H, ∀ e' ∈ H, ¬ prec e' e := by
  classical
  refine hH.elim ?_
  intro a ha
  have : ∀ x : E, x ∈ H → ∃ m ∈ H, ∀ y ∈ H, ¬ prec y m := by
    intro x hx
    -- Well-founded recursion down the precedence relation until a minimal element is reached.
    refine wf.induction x (C := fun x => x ∈ H → ∃ m ∈ H, ∀ y ∈ H, ¬ prec y m) ?_ hx
    intro x ih hx
    by_cases hmin : ∀ y ∈ H, ¬ prec y x
    · exact ⟨x, hx, hmin⟩
    · have hnot : ¬ (∀ y ∈ H, ¬ prec y x) := hmin
      push_neg at hnot
      obtain ⟨y, hyH, hy⟩ := hnot
      have hyx : prec y x := not_not.mp hy
      exact ih y hyx hyH
  exact this a ha

/-- Topological ordering on finite histories by iteratively removing minimal elements. -/
def topoSort
    (prec : Precedence E) [DecidableRel prec] [DecidableEq E]
    (wf : WellFounded prec) :
    ∀ H : Finset E, List E
  | H =>
    if h : H.Nonempty then
      let ⟨e, heH, hmin⟩ := exists_minimal_in (E:=E) prec wf h
      e :: topoSort prec wf (H.erase e)
    else []
  termination_by H => H.card
  decreasing_by
    classical
    simp_wf
    have : (H.erase _) .card < H.card := by
      simpa [Nat.lt_iff_add_one_le, Nat.succ_le_succ_iff] using
        Finset.card_erase_lt_of_mem heH
    simpa using this

/-- `topoSort` covers exactly the elements of `H` with no duplicates. -/
lemma topoSort_perm
    (prec : Precedence E) [DecidableRel prec] [DecidableEq E]
    (wf : WellFounded prec) (H : Finset E) :
    (topoSort (E:=E) prec wf H).Pairwise (· ≠ ·) ∧
    (topoSort (E:=E) prec wf H).toFinset = H := by
  classical
  have hAux : ∀ n, ∀ H : Finset E, H.card = n →
      (topoSort (E:=E) prec wf H).Pairwise (· ≠ ·) ∧
      (topoSort (E:=E) prec wf H).toFinset = H := by
    refine Nat.rec ?base ?step
    · intro H hcard
      have hH : H = (∅ : Finset E) :=
        Finset.card_eq_zero.mp (by simpa [hcard] : H.card = 0)
      have hTop : topoSort (E:=E) prec wf H = [] := by
        simp [topoSort, hH]
      simpa [hTop, hH]
    · intro n ih H hcard
      have hnpos : 0 < H.card := by
        simpa [hcard] using Nat.succ_pos n
      have hn : H.Nonempty := Finset.card_pos.mp hnpos
      obtain ⟨e, heH, hmin⟩ := exists_minimal_in (E:=E) prec wf hn
      have hcard' : (H.erase e).card = n := by
        have : (H.erase e).card + 1 = H.card := Finset.card_erase_add_one heH
        have : (H.erase e).card + 1 = n + 1 := by simpa [hcard] using this
        exact Nat.succ.inj this
      have htail := ih (H.erase e) hcard'
      set tail := topoSort (E:=E) prec wf (H.erase e)
      have hTop : topoSort (E:=E) prec wf H = e :: tail := by
        simp [topoSort, hn, heH, hmin]
      have hxneq : ∀ x ∈ tail, x ≠ e := by
        intro x hx
        have hxErase : x ∈ H.erase e := by
          have : x ∈ tail.toFinset := by
            simpa using List.mem_toFinset.mpr hx
          simpa [tail, htail.2] using this
        exact (Finset.mem_erase.mp hxErase).1
      have hxneq' : ∀ x ∈ tail, e ≠ x := by
        intro x hx
        have hxne := hxneq x hx
        exact fun h => hxne h.symm
      have pairTail : tail.Pairwise (· ≠ ·) := by
        simpa [tail] using htail.1
      refine And.intro ?pair ?cover
      · exact List.Pairwise.cons.2 ⟨hxneq', pairTail⟩
      · simp [hTop, tail, htail.2, Finset.insert_erase, heH]
  exact hAux H.card H rfl

/-- Respect of precedence: earlier elements in `topoSort` have no incoming edges from later ones. -/
lemma topoSort_respects
    (prec : Precedence E) [DecidableRel prec] [DecidableEq E]
    (wf : WellFounded prec) (H : Finset E) :
    ∀ {e₁ e₂}, e₁ ∈ H → e₂ ∈ H → prec e₁ e₂ →
      (topoSort (E:=E) prec wf H).indexOf e₁ <
      (topoSort (E:=E) prec wf H).indexOf e₂ := by
  classical
  have hAux : ∀ n, ∀ H : Finset E, H.card = n →
      ∀ {e₁ e₂}, e₁ ∈ H → e₂ ∈ H → prec e₁ e₂ →
        (topoSort (E:=E) prec wf H).indexOf e₁ <
        (topoSort (E:=E) prec wf H).indexOf e₂ :=
    by
      refine Nat.rec ?base ?step
      · intro H hcard e₁ e₂ h₁ _ _
        have hEmpty : H = (∅ : Finset E) :=
          Finset.card_eq_zero.mp (by simpa [hcard] : H.card = 0)
        simpa [hEmpty] using h₁
      · intro n ih H hcard e₁ e₂ h₁ h₂ h12
        have hnpos : 0 < H.card := by
          simpa [hcard] using Nat.succ_pos n
        have hn : H.Nonempty := Finset.card_pos.mp hnpos
        obtain ⟨e, heH, hmin⟩ := exists_minimal_in (E:=E) prec wf hn
        have hcard' : (H.erase e).card = n := by
          have : (H.erase e).card + 1 = H.card := Finset.card_erase_add_one heH
          have : (H.erase e).card + 1 = n + 1 := by simpa [hcard] using this
          exact Nat.succ.inj this
        set tail := topoSort (E:=E) prec wf (H.erase e)
        have hTop : topoSort (E:=E) prec wf H = e :: tail := by
          simp [topoSort, hn, heH, hmin]
        have h2ne : e₂ ≠ e := by
          intro h
          have : prec e₁ e := by simpa [h] using h12
          exact (hmin e₁ h₁) this
        by_cases h1e : e₁ = e
        · subst h1e
          have hIndex₁ : (topoSort (E:=E) prec wf H).indexOf e = 0 := by
            simp [hTop, List.indexOf_cons]
          have hIndex₂ :
              (topoSort (E:=E) prec wf H).indexOf e₂ =
                (topoSort (E:=E) prec wf (H.erase e)).indexOf e₂ + 1 := by
            simp [hTop, List.indexOf_cons, h2ne]
          have hPos :
              0 < (topoSort (E:=E) prec wf (H.erase e)).indexOf e₂ + 1 :=
            Nat.succ_pos _
          simpa [hIndex₁, hIndex₂] using hPos
        · have h1ne : e₁ ≠ e := h1e
          have h₁mem : e₁ ∈ H.erase e := by
            simpa [Finset.mem_erase, h1ne, h₁]
          have h₂mem : e₂ ∈ H.erase e := by
            simpa [Finset.mem_erase, h2ne, h₂]
          have hIH := ih (H.erase e) hcard' h₁mem h₂mem h12
          have hIndex₁ :
              (topoSort (E:=E) prec wf H).indexOf e₁ =
                (topoSort (E:=E) prec wf (H.erase e)).indexOf e₁ + 1 := by
            simp [hTop, List.indexOf_cons, h1ne]
          have hIndex₂ :
              (topoSort (E:=E) prec wf H).indexOf e₂ =
                (topoSort (E:=E) prec wf (H.erase e)).indexOf e₂ + 1 := by
            simp [hTop, List.indexOf_cons, h2ne]
          simpa [hIndex₁, hIndex₂] using Nat.succ_lt_succ hIH
  exact hAux H.card H rfl

/-- A sequential, one‑per‑tick schedule for a finite history `H`. -/
structure Schedule (E : Type _) where
  order : List E
  nodup : order.Pairwise (· ≠ ·)

namespace Schedule

variable [DecidableEq E]

/-- Event at a given tick (index into the order), if any. -/
def postAtTick (σ : Schedule E) (n : ℕ) : Option E :=
  (σ.order.get? n)

end Schedule

/-- Existence of a one‑per‑tick schedule (finite history version). -/
theorem exists_sequential_schedule
    (prec : Precedence E) [DecidableRel prec] [DecidableEq E]
    (wf : WellFounded prec) (H : Finset E) :
    ∃ σ : Schedule E,
      σ.order.Pairwise (· ≠ ·) ∧
      σ.order.toFinset = H ∧
      (∀ {e₁ e₂}, e₁ ∈ H → e₂ ∈ H → prec e₁ e₂ →
        σ.order.indexOf e₁ < σ.order.indexOf e₂) := by
  classical
  refine ⟨⟨topoSort (E:=E) prec wf H, ?_⟩, ?_, ?_, ?_⟩
  · exact (topoSort_perm (E:=E) prec wf H).1
  · exact (topoSort_perm (E:=E) prec wf H).2
  · intro e₁ e₂ h₁ h₂ h12; exact topoSort_respects (E:=E) prec wf H h₁ h₂ h12

/-- Generic preservation: if conservation holds initially and is preserved
    by single postings, then conservation holds along any sequential schedule
    for a finite history. -/
theorem sequential_preserves_conservation
    {S : Type _} (Conservation : S → Prop) (post : S → E → S)
    (prec : Precedence E)
    [DecidableRel prec] [DecidableEq E]
    (H : Finset E) (σ : Schedule E)
    (hcover : σ.order.toFinset = H)
    (s0 : S)
    (h0 : Conservation s0)
    (preserve_single : ∀ s e, e ∈ H → Conservation s → Conservation (post s e)) :
    Conservation (σ.order.foldl post s0) := by
  classical
  revert s0 h0
  refine σ.order.rec ?base ?step
  · intro s h; simpa using h
  · intro e tail ih s h
    have heH : e ∈ H := by
      have : e ∈ (e :: tail).toFinset := by
        simpa using List.mem_toFinset.mpr (by simp)
      simpa [hcover] using this
    have h' : Conservation (post s e) := preserve_single s e heH h
    simpa using ih (post s e) h'

/-- Atomic tick (finite history): any finite recognition history admits a
    serialization with exactly one posting per tick that respects precedence. -/
theorem atomic_tick
    (prec : Precedence E) [DecidableRel prec] [DecidableEq E]
    (wf : WellFounded prec) (H : Finset E) :
    ∃ σ : Schedule E,
      σ.order.toFinset = H ∧
      ∀ {e₁ e₂}, e₁ ∈ H → e₂ ∈ H → prec e₁ e₂ →
        σ.order.indexOf e₁ < σ.order.indexOf e₂ := by
  classical
  obtain ⟨σ, _nodup, hcover, hrespect⟩ :=
    exists_sequential_schedule (E:=E) prec wf H
  exact ⟨σ, hcover, hrespect⟩

/-- ## Countable serialization --/

section Countable

variable {E : DiscreteEventSystem}
variable (ev : EventEvolution E)
variable [DecidableEq E.Event]

open LedgerNecessity

local notation:max "Prec" => Precedence ev

noncomputable def enum : ℕ → E.Event :=
  Classical.choose (Countable.exists_surjective_nat (E.countable))

lemma enum_surjective : Function.Surjective (enum (E:=E)) :=
  Classical.choose_spec (Countable.exists_surjective_nat (E.countable))

/-- An event is eligible once all predecessors have been posted. -/
def eligible (picked : Finset E.Event) (e : E.Event) : Prop :=
  ∀ {v}, Prec v e → v ∈ picked

lemma eligible_mono {picked₁ picked₂ : Finset E.Event}
    (hsubset : picked₁ ⊆ picked₂) {e : E.Event}
    (helig : eligible (ev:=ev) picked₁ e) :
    eligible (ev:=ev) picked₂ e := by
  intro v hv
  exact hsubset (helig hv)

lemma exists_minimal_eligible (picked : Finset E.Event)
    (h : ∃ e, e ∉ picked) :
    ∃ e, e ∉ picked ∧ eligible (ev:=ev) picked e := by
  classical
  have wf := ledger_prec_wf (ev:=ev)
  let S : Set E.Event := {x | x ∉ picked}
  have hS : S.Nonempty := by
    rcases h with ⟨e, he⟩
    exact ⟨e, he⟩
  obtain ⟨m, hmS, hmin⟩ := wf.has_min S hS
  refine ⟨m, hmS, ?_⟩
  intro v hv
  by_contra hvPicked
  have hvS : v ∈ S := hvPicked
  exact (hmin v hvS hv)

structure Candidate (picked : Finset E.Event) where
  idx : ℕ
  event : E.Event
  event_def : enum (E:=E) idx = event
  not_mem : event ∉ picked
  eligible_event : eligible (ev:=ev) picked event

lemma exists_candidate_index (picked : Finset E.Event)
    (h : ∃ e, e ∉ picked) :
    ∃ n, enum (E:=E) n ∉ picked ∧ eligible (ev:=ev) picked (enum (E:=E) n) := by
  classical
  obtain ⟨e, heNot, helig⟩ := exists_minimal_eligible (ev:=ev) (E:=E) picked h
  obtain ⟨n, hn⟩ := enum_surjective (E:=E) e
  refine ⟨n, ?_, ?_⟩
  · simpa [hn]
  · simpa [hn] using helig

noncomputable def chooseCandidate (picked : Finset E.Event) :
    Option (Candidate (ev:=ev) (E:=E) picked) :=
  if h : ∃ e, e ∉ picked then
    let hx := exists_candidate_index (ev:=ev) (E:=E) picked h
    let n := Nat.find hx
    let hn := Nat.find_spec hx
    let e := enum (E:=E) n
    some
      { idx := n
      , event := e
      , event_def := rfl
      , not_mem := hn.left
      , eligible_event := hn.right }
  else
    none

lemma chooseCandidate_none_iff (picked : Finset E.Event) :
    chooseCandidate (ev:=ev) (E:=E) picked = none ↔
      ¬∃ e, e ∉ picked := by
  classical
  unfold chooseCandidate
  split_ifs with h
  · simp [h]
  · simp [h]

lemma chooseCandidate_some_spec {picked : Finset E.Event}
    {c : Candidate (ev:=ev) (E:=E) picked}
    (h : chooseCandidate (ev:=ev) (E:=E) picked = some c) :
    c.not_mem ∧ eligible (ev:=ev) picked c.event := by
  classical
  unfold chooseCandidate at h
  split_ifs at h with hExists
  · rcases h with ⟨⟩
    simp
  · cases h

/-- Minimal index (in the fixed enumeration `enum`) where an event appears. -/
noncomputable def minIndex (e : E.Event) : ℕ :=
  Nat.find (enum_surjective (E:=E) e)

lemma minIndex_spec (e : E.Event) : enum (E:=E) (minIndex (E:=E) e) = e := by
  classical
  unfold minIndex
  exact Nat.find_spec (enum_surjective (E:=E) e)

lemma minIndex_min (e : E.Event) {n : ℕ} (h : enum (E:=E) n = e) :
    minIndex (E:=E) e ≤ n := by
  classical
  unfold minIndex
  exact Nat.find_min' (enum_surjective (E:=E) e) h

/-- A canonical countable schedule derived from `minIndex`. Each event appears
    exactly once at its minimal enumeration index. -/
noncomputable def scheduleByMinIndex : CountableSchedule E.Event :=
{ postAt := fun n =>
    if h : ∃ e : E.Event, minIndex (E:=E) e = n then
      some (Classical.choose h)
    else none
, nodup := by
    intro n₁ n₂ e h₁ h₂
    classical
    unfold scheduleByMinIndex at h₁ h₂
    simp only at h₁ h₂
    rcases Classical.decEq (∃ e, minIndex (E:=E) e = n₁) with hdec₁ | hdec₁
    · simp [scheduleByMinIndex._match_1, hdec₁] at h₁
    · rcases h₁
    rcases Classical.decEq (∃ e, minIndex (E:=E) e = n₂) with hdec₂ | hdec₂
    · simp [scheduleByMinIndex._match_1, hdec₂] at h₂
    · rcases h₂
    -- In the `some` branches on both sides
    have hsome₁ : ∃ e, minIndex (E:=E) e = n₁ := by
      by_contra H; simp [scheduleByMinIndex._match_1, H] at h₁
    have hsome₂ : ∃ e, minIndex (E:=E) e = n₂ := by
      by_contra H; simp [scheduleByMinIndex._match_1, H] at h₂
    let e₁ := Classical.choose hsome₁
    let e₂ := Classical.choose hsome₂
    have he₁ : minIndex (E:=E) e₁ = n₁ := (Classical.choose_spec hsome₁)
    have he₂ : minIndex (E:=E) e₂ = n₂ := (Classical.choose_spec hsome₂)
    -- The `some` payloads must coincide with `e`
    have : e₁ = e := by
      have : some e₁ = some e := by simpa [scheduleByMinIndex._match_1, he₁] using h₁
      exact by cases this; rfl
    have : e₂ = e := by
      have : some e₂ = some e := by simpa [scheduleByMinIndex._match_1, he₂] using h₂
      exact by cases this; rfl
    -- Conclude equality of indices by injectivity of `minIndex`
    simpa [this, he₁, he₂]
, complete := by
    intro e
    classical
    refine ⟨minIndex (E:=E) e, ?_⟩
    simp [scheduleByMinIndex, scheduleByMinIndex._match_1, minIndex_spec (E:=E) e]
      -- exhibits the chosen `e` at its minimal index
}

/-- Countable atomic schedule (enumerative). Posts exactly one event per tick,
    visits every event, with no duplicates. -/
theorem atomic_tick_countable :
    ∃ σ : CountableSchedule E.Event,
      (∀ e, ∃ n, σ.postAt n = some e) ∧
      (∀ {n₁ n₂ e}, σ.postAt n₁ = some e → σ.postAt n₂ = some e → n₁ = n₂) := by
  classical
  refine ⟨scheduleByMinIndex (ev:=ev), ?_, ?_⟩
  · intro e; exact (scheduleByMinIndex (ev:=ev)).complete e
  · intro n₁ n₂ e h₁ h₂; exact (scheduleByMinIndex (ev:=ev)).nodup h₁ h₂

end Countable

end Atomicity

end Foundation
end IndisputableMonolith
