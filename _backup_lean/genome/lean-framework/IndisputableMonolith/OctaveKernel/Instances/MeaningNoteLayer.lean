import IndisputableMonolith.OctaveKernel.Basic
import IndisputableMonolith.Genetics.MeaningNote

namespace IndisputableMonolith
namespace OctaveKernel
namespace Instances

open IndisputableMonolith.Genetics

/-!
# OctaveKernel.Instances.MeaningNoteLayer

This module provides an `OctaveKernel.Layer` witness for the “same note across layers”
artifact (`Genetics.MeaningNote`).

Design:
- **State**: a `MeaningNote` plus an unbounded tick counter
- **Phase**: `tick % 8`
- **Cost**: trivial `0`
- **Admissible**: `True`
- **Step**: increments tick (note stays fixed)

This is intentionally conservative: it makes no claim about dynamics, only that this
typed cross-layer “note” can live inside the shared 8-beat interface.
-/

/-- Minimal state: a fixed note plus an 8-phase tick counter. -/
structure MeaningNoteState where
  note : MeaningNote
  tick : ℕ

namespace MeaningNoteState

/-- Advance one beat (tick increments; note unchanged). -/
def advance (s : MeaningNoteState) : MeaningNoteState :=
  { s with tick := s.tick + 1 }

/-- Phase is tick mod 8. -/
def phase8 (s : MeaningNoteState) : Fin 8 :=
  ⟨s.tick % 8, Nat.mod_lt _ (by decide)⟩

end MeaningNoteState

/-- The MeaningNote layer witness. -/
def MeaningNoteLayer : Layer :=
{ State := MeaningNoteState
, phase := MeaningNoteState.phase8
, cost := fun _ => 0
, admissible := fun _ => True
, step := MeaningNoteState.advance
}

/-- Stepping advances phase by one (mod 8). -/
theorem MeaningNoteLayer_stepAdvances : Layer.StepAdvances MeaningNoteLayer := by
  intro s
  ext
  -- Reduce to a Nat equality on `Fin.val`.
  simp only [MeaningNoteLayer, MeaningNoteState.advance, MeaningNoteState.phase8,
    Fin.val_add, Fin.val_one]
  -- (t+1) % 8 = (t % 8 + 1) % 8
  simp [Nat.add_mod]

/-- Trivial ledger: all states admissible. -/
theorem MeaningNoteLayer_preservesAdmissible : Layer.PreservesAdmissible MeaningNoteLayer := by
  intro _s hs
  exact hs

/-- Trivial cost: always nonincreasing. -/
theorem MeaningNoteLayer_nonincreasingCost : Layer.NonincreasingCost MeaningNoteLayer := by
  intro _s _hs
  simp [MeaningNoteLayer, MeaningNoteState.advance]

end Instances
end OctaveKernel
end IndisputableMonolith
