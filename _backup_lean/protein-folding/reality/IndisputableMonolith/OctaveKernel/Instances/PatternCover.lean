import IndisputableMonolith.OctaveKernel.Basic
import IndisputableMonolith.Patterns
import IndisputableMonolith.Patterns.GrayCycle

namespace IndisputableMonolith
namespace OctaveKernel
namespace Instances

open Classical
open IndisputableMonolith.Patterns

/-!
# OctaveKernel.Instances.PatternCover

An extremely small “witness” instance showing that the 8-beat clock can be
realized from the existing `Patterns` results.

This is intentionally conservative:
- It does **not** claim that this instance is “physics”.
- It packages a **rigorous 3-bit Gray cycle** (adjacent one-bit steps, period 8,
  and a complete cover) into the `OctaveKernel.Layer` interface so later bridge
  theorems can be stated cleanly.
-/

/-- Interpret a phase index as the corresponding 3-bit pattern on the canonical Gray-8 cycle. -/
noncomputable def patternAtPhase (t : Phase) : Pattern 3 :=
  Patterns.grayCycle3Path t

/-- The observation `patternAtPhase` hits every 3-bit pattern (it is a complete cover). -/
theorem patternAtPhase_surjective : Function.Surjective patternAtPhase := by
  simpa [patternAtPhase] using Patterns.grayCycle3_surjective

/-- Consecutive phases differ by exactly one bit (Gray adjacency). -/
theorem patternAtPhase_oneBit_step (t : Phase) :
    Patterns.OneBitDiff (patternAtPhase t) (patternAtPhase (t + 1)) := by
  simpa [patternAtPhase] using (Patterns.grayCycle3_oneBit_step (i := t))

/-- A minimal “octave layer” whose state is just the 8-phase clock.

We attach the `Patterns` content through the `patternAtPhase` observation
function rather than baking it into the state. -/
noncomputable def PatternCoverLayer : Layer :=
{ State := Phase
, phase := fun s => s
, cost := fun _ => 0
, admissible := fun _ => True
, step := fun s => s + 1
}

theorem PatternCoverLayer_stepAdvances : Layer.StepAdvances PatternCoverLayer := by
  intro s
  rfl

theorem PatternCoverLayer_preservesAdmissible : Layer.PreservesAdmissible PatternCoverLayer := by
  intro s hs
  trivial

theorem PatternCoverLayer_nonincreasingCost : Layer.NonincreasingCost PatternCoverLayer := by
  intro s hs
  simp [PatternCoverLayer]

/-- Observation channel: the 3-bit pattern realized at each phase tick. -/
noncomputable def PatternCoverChannel : Channel PatternCoverLayer :=
{ Obs := Pattern 3
, observe := patternAtPhase
, quality := fun _ => 0
}

end Instances
end OctaveKernel
end IndisputableMonolith
