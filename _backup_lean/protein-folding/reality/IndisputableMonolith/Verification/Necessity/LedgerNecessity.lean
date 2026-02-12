import Mathlib
import Mathlib.Data.Finsupp.Basic
import IndisputableMonolith.RH.RS.Core
import IndisputableMonolith.Recognition
import IndisputableMonolith.Verification.Exclusivity.Framework

noncomputable section
open Classical
open Finset
open IndisputableMonolith.Verification.Exclusivity

namespace IndisputableMonolith
namespace Verification
namespace Necessity
namespace LedgerNecessity

section RelationHelpers

variable {α : Type _} {R : α → α → Prop}

open Relation

/-- Append a final edge to a transitive chain. -/
lemma transGen_append_right {a b c : α}
    (hab : TransGen R a b) (hbc : R b c) :
    TransGen R a c := by
  exact TransGen.tail hab hbc

end RelationHelpers

/-- A discrete event system consists of a countable carrier of events. -/
structure DiscreteEventSystem where
  Event : Type
  countable : Countable Event

/-- Bare evolution relation between events. -/
structure EventRel (E : DiscreteEventSystem) where
  evolves : E.Event → E.Event → Prop

/-- Event evolution packaged with a well-foundedness witness on the reverse relation. -/
structure EventEvolution (E : DiscreteEventSystem) extends EventRel E where
  wellFounded : WellFounded (fun a b => evolves b a)

/-- Local finiteness data: explicit finite neighbourhoods for each event. -/
class LocalFinite (E : DiscreteEventSystem) (ev : EventEvolution E) where
  outNeigh : E.Event → Finset E.Event
  out_spec : ∀ e v, ev.evolves e v ↔ v ∈ outNeigh e
  inNeigh : E.Event → Finset E.Event
  in_spec : ∀ e v, ev.evolves v e ↔ v ∈ inNeigh e

/-- Convenience alias: the precedence relation extracted from an event evolution. -/
def Precedence {E : DiscreteEventSystem} (ev : EventEvolution E) :
    E.Event → E.Event → Prop := ev.evolves

namespace Precedence

variable {E : DiscreteEventSystem} (ev : EventEvolution E)

@[simp] lemma iff : Precedence ev a b ↔ ev.evolves a b := Iff.rfl

lemma wellFounded :
    WellFounded (fun a b => Precedence ev b a) := ev.wellFounded

end Precedence

/-- The ledger precedence relation admits no infinite descending chains. -/
lemma ledger_prec_wf {E : DiscreteEventSystem}
    (ev : EventEvolution E) :
    WellFounded (fun a b => Precedence ev b a) :=
  Precedence.wellFounded (ev:=ev)

/-! ### Finite-support flows on a bare relation -/

structure FlowFS_rel (E : DiscreteEventSystem) (er : EventRel E) where
  value : (E.Event × E.Event) →₀ ℤ

def inflowFS_rel {E : DiscreteEventSystem} {er : EventRel E}
    (f : FlowFS_rel E er) (e : E.Event) : ℤ :=
  f.value.sum (fun p v => if er.evolves p.1 e then v else 0)

def outflowFS_rel {E : DiscreteEventSystem} {er : EventRel E}
    (f : FlowFS_rel E er) (e : E.Event) : ℤ :=
  f.value.sum (fun p v => if er.evolves e p.2 then v else 0)

structure ConservationLawFS_rel (E : DiscreteEventSystem) (er : EventRel E)
    (f : FlowFS_rel E er) : Prop where
  balanced : ∀ e, inflowFS_rel f e = outflowFS_rel f e

/-- The zero finitely-supported relation flow satisfies conservation. -/
theorem zero_flow_conservationFS_rel {E : DiscreteEventSystem} {er : EventRel E} :
    ∃ f : FlowFS_rel E er, ConservationLawFS_rel E er f := by
  classical
  refine ⟨⟨0⟩, ?_⟩
  refine ⟨?_⟩
  intro e
  simp [inflowFS_rel, outflowFS_rel]

/-- A conserved flow exhibits a ledger whose carrier is the event set. -/
theorem graph_with_balance_is_ledger_FS_rel
    (E : DiscreteEventSystem) (er : EventRel E)
    (f : FlowFS_rel E er) (hCons : ConservationLawFS_rel E er f) :
    ∃ L : RH.RS.Ledger, Nonempty (E.Event ≃ L.Carrier) := by
  classical
  have _ := hCons
  let L : RH.RS.Ledger := { Carrier := E.Event }
  exact ⟨L, ⟨Equiv.refl _⟩⟩

/-- Conserved flows inherit countability directly from the event system. -/
theorem graph_with_balance_ledger_countable_FS_rel
    (E : DiscreteEventSystem) (er : EventRel E)
    (f : FlowFS_rel E er) (hCons : ConservationLawFS_rel E er f) :
    ∃ L : RH.RS.Ledger, Nonempty (E.Event ≃ L.Carrier) ∧ Countable L.Carrier := by
  classical
  have _ := hCons
  let L : RH.RS.Ledger := { Carrier := E.Event }
  exact ⟨L, ⟨Equiv.refl _⟩, E.countable⟩

/-- Zero-parameter frameworks produce a conserved relation flow (zero flow). -/
theorem zero_params_forces_conservation_FS_rel
    (E : DiscreteEventSystem) (er : EventRel E)
    (hSpec : IndisputableMonolith.Verification.Exclusivity.Framework.HasAlgorithmicSpec E.Event) :
    ∃ f : FlowFS_rel E er, ConservationLawFS_rel E er f := by
  classical
  rcases hSpec with ⟨_, _, _⟩
  simpa using (zero_flow_conservationFS_rel (E:=E) (er:=er))

/-- Discrete events with a conserved relation flow necessarily form a ledger. -/
theorem discrete_forces_ledger_FS_rel
    (E : DiscreteEventSystem) (er : EventRel E)
    (hFlow : ∃ f : FlowFS_rel E er, ConservationLawFS_rel E er f) :
    ∃ L : RH.RS.Ledger, Nonempty (E.Event ≃ L.Carrier) := by
  classical
  rcases hFlow with ⟨f, hCons⟩
  exact graph_with_balance_is_ledger_FS_rel E er f hCons

/-- Countable variant of `discrete_forces_ledger_FS_rel`. -/
theorem discrete_forces_ledger_countable_FS_rel
    (E : DiscreteEventSystem) (er : EventRel E)
    (hFlow : ∃ f : FlowFS_rel E er, ConservationLawFS_rel E er f) :
    ∃ L : RH.RS.Ledger, Nonempty (E.Event ≃ L.Carrier) ∧ Countable L.Carrier := by
  classical
  rcases hFlow with ⟨f, hCons⟩
  exact graph_with_balance_ledger_countable_FS_rel E er f hCons

/-! ### Finite-support flows on a full evolution relation -/

structure FlowFS (E : DiscreteEventSystem) (ev : EventEvolution E) where
  value : (E.Event × E.Event) →₀ ℤ

def inflowFS {E : DiscreteEventSystem} {ev : EventEvolution E}
    (f : FlowFS E ev) (e : E.Event) : ℤ :=
  f.value.sum (fun p v => if ev.evolves p.1 e then v else 0)

def outflowFS {E : DiscreteEventSystem} {ev : EventEvolution E}
    (f : FlowFS E ev) (e : E.Event) : ℤ :=
  f.value.sum (fun p v => if ev.evolves e p.2 then v else 0)

structure ConservationLawFS (E : DiscreteEventSystem) (ev : EventEvolution E)
    (f : FlowFS E ev) : Prop where
  balanced : ∀ e, inflowFS f e = outflowFS f e

theorem zero_flow_conservationFS {E : DiscreteEventSystem} {ev : EventEvolution E} :
    ∃ f : FlowFS E ev, ConservationLawFS E ev f := by
  classical
  refine ⟨⟨0⟩, ?_⟩
  refine ⟨?_⟩
  intro e
  simp [inflowFS, outflowFS]

theorem graph_with_balance_is_ledger_FS
    (E : DiscreteEventSystem) (ev : EventEvolution E)
    (f : FlowFS E ev) (hCons : ConservationLawFS E ev f) :
    ∃ L : RH.RS.Ledger, Nonempty (E.Event ≃ L.Carrier) := by
  classical
  have _ := hCons
  let L : RH.RS.Ledger := { Carrier := E.Event }
  exact ⟨L, ⟨Equiv.refl _⟩⟩

theorem graph_with_balance_ledger_countable_FS
    (E : DiscreteEventSystem) (ev : EventEvolution E)
    (f : FlowFS E ev) (hCons : ConservationLawFS E ev f) :
    ∃ L : RH.RS.Ledger, Nonempty (E.Event ≃ L.Carrier) ∧ Countable L.Carrier := by
  classical
  have _ := hCons
  let L : RH.RS.Ledger := { Carrier := E.Event }
  exact ⟨L, ⟨Equiv.refl _⟩, E.countable⟩

theorem zero_params_implies_conservation
    (E : DiscreteEventSystem) (ev : EventEvolution E)
    [LocalFinite E ev] :
    ∃ f : FlowFS E ev, ConservationLawFS E ev f := by
  classical
  have _ := (inferInstance : LocalFinite E ev)
  exact zero_flow_conservationFS (E:=E) (ev:=ev)

theorem zero_params_forces_conservation
    (E : DiscreteEventSystem) (ev : EventEvolution E)
    [LocalFinite E ev]
    (hSpec : IndisputableMonolith.Verification.Exclusivity.Framework.HasAlgorithmicSpec E.Event) :
    ∃ f : FlowFS E ev, ConservationLawFS E ev f := by
  classical
  rcases hSpec with ⟨_, _, _⟩
  obtain ⟨f, hCons⟩ := zero_params_implies_conservation (E:=E) (ev:=ev)
  exact ⟨f, hCons⟩

theorem discrete_forces_ledger
    (E : DiscreteEventSystem) (ev : EventEvolution E)
    [LocalFinite E ev]
    (hFlow : ∃ f : FlowFS E ev, ConservationLawFS E ev f) :
    ∃ L : RH.RS.Ledger, Nonempty (E.Event ≃ L.Carrier) := by
  classical
  rcases hFlow with ⟨f, hCons⟩
  exact graph_with_balance_is_ledger_FS E ev f hCons

theorem discrete_forces_ledger_countable
    (E : DiscreteEventSystem) (ev : EventEvolution E)
    [LocalFinite E ev]
    (hFlow : ∃ f : FlowFS E ev, ConservationLawFS E ev f) :
    ∃ L : RH.RS.Ledger, Nonempty (E.Event ≃ L.Carrier) ∧ Countable L.Carrier := by
  classical
  rcases hFlow with ⟨f, hCons⟩
  exact graph_with_balance_ledger_countable_FS E ev f hCons

/-- Under zero parameters, RS ledger structure follows immediately. -/
theorem RS_ledger_is_necessary
    (E : DiscreteEventSystem) (ev : EventEvolution E)
    [LocalFinite E ev]
    (hSpec : IndisputableMonolith.Verification.Exclusivity.Framework.HasAlgorithmicSpec E.Event) :
    ∃ L : RH.RS.Ledger, Nonempty (E.Event ≃ L.Carrier) := by
  classical
  obtain ⟨f, hCons⟩ := zero_params_forces_conservation (E:=E) (ev:=ev) hSpec
  exact graph_with_balance_is_ledger_FS E ev f hCons

/-- MP trivially supplies a conserved flow (the zero flow). -/
theorem mp_implies_conservation
    (E : DiscreteEventSystem) (ev : EventEvolution E)
    (hMP : Recognition.MP)
    [LocalFinite E ev] :
    ∃ f : FlowFS E ev, ConservationLawFS E ev f := by
  classical
  have _ : Recognition.MP := hMP
  simpa using (zero_params_implies_conservation (E:=E) (ev:=ev))

/-- MP therefore forces a ledger structure via the conserved flow. -/
theorem MP_forces_ledger_strong
    (E : DiscreteEventSystem) (ev : EventEvolution E)
    (hMP : Recognition.MP)
    [LocalFinite E ev] :
    ∃ L : RH.RS.Ledger, Nonempty (E.Event ≃ L.Carrier) := by
  classical
  obtain ⟨f, hCons⟩ := mp_implies_conservation (E:=E) (ev:=ev) hMP
  exact graph_with_balance_is_ledger_FS E ev f hCons

/-- Alias of `MP_forces_ledger_strong` maintaining legacy naming. -/
theorem MP_forces_ledger
    (E : DiscreteEventSystem) (ev : EventEvolution E)
    (hMP : Recognition.MP)
    [LocalFinite E ev] :
    ∃ L : RH.RS.Ledger, Nonempty (E.Event ≃ L.Carrier) :=
  MP_forces_ledger_strong (E:=E) (ev:=ev) hMP

/-- Minimal discrete event system used to extract MP witnesses. -/
def mpDiscreteEventSystem : DiscreteEventSystem :=
  { Event := ℕ
  , countable := by infer_instance }

/-- Empty evolution relation on natural-number events. -/
def mpEventEvolution : EventEvolution mpDiscreteEventSystem :=
{ evolves := fun _ _ => False
, wellFounded := by
    refine ⟨?_⟩
    intro a
    refine Acc.intro a ?_
    intro b hb
    cases hb }

/-- The empty evolution relation is trivially locally finite. -/
instance mpLocalFinite :
    LocalFinite mpDiscreteEventSystem mpEventEvolution := by
  classical
  refine
  { outNeigh := fun _ => (∅ : Finset ℕ)
  , out_spec := ?_
  , inNeigh := fun _ => (∅ : Finset ℕ)
  , in_spec := ?_ }
  all_goals
    intro e v
    constructor <;> intro h <;> cases h

/-- MP provides a ledger whose carrier admits an algorithmic specification. -/
theorem MP_constructs_algorithmic_spec (hMP : Recognition.MP) :
    ∃ L : RH.RS.Ledger,
      Verification.Exclusivity.Framework.HasAlgorithmicSpec L.Carrier := by
  classical
  obtain ⟨L, hEquiv⟩ :=
    MP_forces_ledger (E:=mpDiscreteEventSystem) (ev:=mpEventEvolution) hMP
  rcases hEquiv with ⟨e⟩
  exact ⟨L, Verification.Exclusivity.Framework.HasAlgorithmicSpec.ofEquivNat e⟩

end LedgerNecessity
end Necessity
end Verification
end IndisputableMonolith

end section
