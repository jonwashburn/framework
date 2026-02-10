import Mathlib

namespace IndisputableMonolith
namespace OctaveKernel

/-!
# OctaveKernel.Basic

Minimal, reusable kernel for the “Octave System”.

This file intentionally contains **only definitions**. Theorems and domain
instances are added in later milestones.

Claim hygiene:
- `Layer` is a *definition* (a packaging of primitives).
- Properties like `StepAdvances` are *predicates* (to be proved per layer).
- Cross-domain identifications are **not** made here.
-/

/-- The canonical 8-beat phase index. -/
abbrev Phase := Fin 8

/-- A generic “octave layer”: a state space with an 8-phase clock, a cost/strain,
and an admissibility (ledger) predicate. -/
structure Layer where
  /-- State space for this layer. -/
  State : Type
  /-- 8-phase clock position of a state. -/
  phase : State → Phase
  /-- Cost/strain functional (ordering is typically what matters). -/
  cost : State → ℝ
  /-- Admissible (ledger-legal) states. -/
  admissible : State → Prop
  /-- One-step evolution map (interpretation depends on the layer). -/
  step : State → State

namespace Layer

/-- Phase after one step. -/
def stepPhase (L : Layer) (s : L.State) : Phase :=
  L.phase (L.step s)

/-- Predicate: evolution advances phase by one beat (mod 8). -/
def StepAdvances (L : Layer) : Prop :=
  ∀ s, L.phase (L.step s) = L.phase s + 1

/-- Predicate: admissibility (ledger-closure) is preserved under evolution. -/
def PreservesAdmissible (L : Layer) : Prop :=
  ∀ s, L.admissible s → L.admissible (L.step s)

/-- Predicate: evolution is non-increasing in cost on admissible states. -/
def NonincreasingCost (L : Layer) : Prop :=
  ∀ s, L.admissible s → L.cost (L.step s) ≤ L.cost s

end Layer

/-- A measurement/display channel attached to a layer. -/
structure Channel (L : Layer) where
  /-- Observation type. -/
  Obs : Type
  /-- Observation map from state to observation. -/
  observe : L.State → Obs
  /-- A real-valued quality functional on observations (lower is “better” by convention). -/
  quality : Obs → ℝ

namespace Channel

/-- Quality of a state through a channel. -/
def stateQuality {L : Layer} (C : Channel L) (s : L.State) : ℝ :=
  C.quality (C.observe s)

end Channel

end OctaveKernel
end IndisputableMonolith
