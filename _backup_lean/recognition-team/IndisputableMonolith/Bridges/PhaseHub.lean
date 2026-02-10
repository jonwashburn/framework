import IndisputableMonolith.OctaveKernel.Basic
import IndisputableMonolith.OctaveKernel.Bridges.Basic

namespace IndisputableMonolith
namespace OctaveKernel
namespace Bridges

/-!
# OctaveKernel.Bridges.PhaseHub

This module introduces a canonical "hub layer" for phase-only reasoning:

- `PhaseLayer`: the pure 8-phase clock as a `Layer`.
- `phaseProjectionBridge`: given any layer that satisfies `Layer.StepAdvances`,
  we build a `Bridge` into `PhaseLayer`.

This is a safe first bridge: it does not assert any cross-domain empirical
identification; it only repackages each layer's already-defined `phase`.
-/

/-- A canonical phase-only layer.

State is just `Phase = Fin 8`, phase is identity, step is `+1`.
Costs/admissibility are intentionally trivial (0 / True).
-/
def PhaseLayer : Layer :=
{ State := Phase
, phase := fun p => p
, cost := fun _ => 0
, admissible := fun _ => True
, step := fun p => p + 1
}

theorem PhaseLayer_stepAdvances : Layer.StepAdvances PhaseLayer := by
  intro _p
  rfl

theorem PhaseLayer_preservesAdmissible : Layer.PreservesAdmissible PhaseLayer := by
  intro _p hp
  trivial

theorem PhaseLayer_nonincreasingCost : Layer.NonincreasingCost PhaseLayer := by
  intro _p hp
  simp [PhaseLayer]

/-- Project any layer state to its phase. -/
def phaseProjection (L : Layer) : L.State → Phase :=
  L.phase

/-- If a layer advances phase by one step, then phase-projection defines a `Bridge`
into the canonical `PhaseLayer`. -/
def phaseProjectionBridge (L : Layer) (hAdv : Layer.StepAdvances L) :
    Bridge L PhaseLayer :=
{ map := phaseProjection L
, preservesPhase := by
    intro s
    rfl
, commutesStep := by
    intro s
    -- `PhaseLayer.step` is `+1`, so commuting is exactly `StepAdvances`.
    simpa [PhaseLayer, phaseProjection] using hAdv s
}

/-! ## Alignment relation (bridge-free but typed) -/

/-- Two states are phase-aligned if their phases agree. -/
def Aligned (L₁ L₂ : Layer) (s₁ : L₁.State) (s₂ : L₂.State) : Prop :=
  L₁.phase s₁ = L₂.phase s₂

/-- If both layers satisfy `StepAdvances`, alignment is preserved by stepping both sides. -/
theorem aligned_step {L₁ L₂ : Layer}
    (h₁ : Layer.StepAdvances L₁) (h₂ : Layer.StepAdvances L₂)
    {s₁ : L₁.State} {s₂ : L₂.State} :
    Aligned L₁ L₂ s₁ s₂ → Aligned L₁ L₂ (L₁.step s₁) (L₂.step s₂) := by
  intro h
  unfold Aligned at *
  calc
    L₁.phase (L₁.step s₁) = L₁.phase s₁ + 1 := h₁ s₁
    _ = L₂.phase s₂ + 1 := by simpa [h]
    _ = L₂.phase (L₂.step s₂) := by simpa using (h₂ s₂).symm

/-- Alignment is preserved by iterating both steps the same number of times. -/
theorem aligned_iterate {L₁ L₂ : Layer}
    (h₁ : Layer.StepAdvances L₁) (h₂ : Layer.StepAdvances L₂) :
    ∀ n s₁ s₂, Aligned L₁ L₂ s₁ s₂ →
      Aligned L₁ L₂ (Function.iterate L₁.step n s₁) (Function.iterate L₂.step n s₂) := by
  intro n
  induction n with
  | zero =>
      intro s₁ s₂ h
      simpa [Aligned] using h
  | succ n ih =>
      intro s₁ s₂ h
      have hAlignedN :
          Aligned L₁ L₂ (Function.iterate L₁.step n s₁) (Function.iterate L₂.step n s₂) :=
        ih s₁ s₂ h
      have hStep :
          Aligned L₁ L₂
            (L₁.step (Function.iterate L₁.step n s₁))
            (L₂.step (Function.iterate L₂.step n s₂)) :=
        aligned_step (L₁ := L₁) (L₂ := L₂) h₁ h₂ hAlignedN
      -- Rewrite iterates (n+1) as one step after iterate n.
      simpa [Function.iterate, Function.iterate_succ_apply'] using hStep

end Bridges
end OctaveKernel
end IndisputableMonolith
