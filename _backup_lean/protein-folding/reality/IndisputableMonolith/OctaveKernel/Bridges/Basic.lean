import IndisputableMonolith.OctaveKernel.Basic
import IndisputableMonolith.Compat.FunctionIterate

namespace IndisputableMonolith
namespace OctaveKernel

/-!
# OctaveKernel.Bridges.Basic

This file introduces a minimal notion of a **bridge** between two octave layers.

Claim hygiene:
- `Bridge` is a **definition** (typed map + structural preservation fields).
- Lemmas in `Bridge` namespace are **theorems** about bridges.
- No empirical identifications appear here.
-/

/-- A structure-preserving map between two `Layer`s.

The intended reading is: `map` translates states of `L₁` into states of `L₂`,
preserving the 8-phase clock and commuting with one-step dynamics.

This is the minimal ingredient needed to *transfer* phase-based invariants across layers.
-/
structure Bridge (L₁ L₂ : Layer) where
  /-- Map states from `L₁` to `L₂`. -/
  map : L₁.State → L₂.State
  /-- Preserve the 8-phase clock. -/
  preservesPhase : ∀ s, L₂.phase (map s) = L₁.phase s
  /-- Commute with one-step evolution. -/
  commutesStep : ∀ s, map (L₁.step s) = L₂.step (map s)

namespace Bridge

variable {L₁ L₂ L₃ : Layer}

/-- Compose bridges. -/
def comp (B₁₂ : Bridge L₁ L₂) (B₂₃ : Bridge L₂ L₃) : Bridge L₁ L₃ :=
{ map := fun s => B₂₃.map (B₁₂.map s)
, preservesPhase := by
    intro s
    simpa [B₂₃.preservesPhase, B₁₂.preservesPhase]
, commutesStep := by
    intro s
    simpa [B₂₃.commutesStep, B₁₂.commutesStep]
}

/-- A bridge commutes with any finite iterate of the step function. -/
theorem map_iterate (B : Bridge L₁ L₂) :
    ∀ n s, B.map (Function.iterate L₁.step n s) = Function.iterate L₂.step n (B.map s) := by
  intro n
  induction n with
  | zero =>
      intro s
      simp [Function.iterate]
  | succ n ih =>
      intro s
      -- iterate (n+1) = step ∘ iterate n
      -- Unfold the compat `Function.iterate` once on both sides.
      -- After unfolding, this is exactly the induction hypothesis applied to `L₁.step s`,
      -- with one rewrite using `commutesStep`.
      have ih' :
          B.map (Nat.iterate L₁.step n (L₁.step s)) =
            Nat.iterate L₂.step n (B.map (L₁.step s)) := by
        simpa [Function.iterate] using ih (L₁.step s)
      simpa [Function.iterate, Nat.iterate, B.commutesStep s] using ih'

/-- Phase alignment is preserved across iterated stepping via a bridge. -/
theorem phase_iterate (B : Bridge L₁ L₂) (n : ℕ) (s : L₁.State) :
    L₂.phase (Function.iterate L₂.step n (B.map s)) = L₁.phase (Function.iterate L₁.step n s) := by
  have h := B.preservesPhase (Function.iterate L₁.step n s)
  -- Rewrite the LHS using the iterate-commutation lemma.
  simpa [Bridge.map_iterate (B := B) n s] using h

/-- Transfer `StepAdvances` across a *surjective* bridge. -/
theorem stepAdvances_of_surjective (B : Bridge L₁ L₂)
    (hAdv₁ : Layer.StepAdvances L₁)
    (hSurj : Function.Surjective B.map) :
    Layer.StepAdvances L₂ := by
  intro t
  rcases hSurj t with ⟨s, rfl⟩
  -- Reduce the goal to the preimage `s`.
  have hStepPhase : L₂.phase (L₂.step (B.map s)) = L₂.phase (B.map (L₁.step s)) := by
    simpa using (congrArg L₂.phase (B.commutesStep s)).symm
  calc
    L₂.phase (L₂.step (B.map s))
        = L₂.phase (B.map (L₁.step s)) := hStepPhase
    _   = L₁.phase (L₁.step s) := by simpa using (B.preservesPhase (L₁.step s))
    _   = L₁.phase s + 1 := hAdv₁ s
    _   = L₂.phase (B.map s) + 1 := by simpa [B.preservesPhase s]

end Bridge

end OctaveKernel
end IndisputableMonolith
