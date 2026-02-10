import Mathlib
import IndisputableMonolith.Patterns.GrayCycle
import IndisputableMonolith.OctaveKernel.Instances.PatternCover

/-!
# Octave Theorem Bundle (core)

This module is a **single canonical import path** for the core “octave” facts
that are purely mathematical / definitional:

- The 8-phase clock (`OctaveKernel.Phase = Fin 8`) closes after 8 steps.
- There is a concrete 3-bit Gray cycle (period 8) in `Patterns.GrayCycle`.
- The conservative OctaveKernel witness layer `PatternCoverLayer` observes that
  Gray cycle as `patternAtPhase`, and consecutive phases differ by one bit.

Claim hygiene:
- Everything in this file is `THEOREM`/`DEF` level (no empirical inputs).
- Any “ledger ⇒ adjacency” bridge is *not* included here (see planned Workstream B).
-/

namespace IndisputableMonolith
namespace Octave

noncomputable section

abbrev Phase := OctaveKernel.Phase

/-! ## Pure clock closure -/

theorem phase_add8 (p : Phase) : p + 8 = p := by
  -- `Fin` addition is modulo; `8` is `0` in `Fin 8`.
  simp

theorem phase_add1_iter8 (p : Phase) : (Nat.iterate (fun q : Phase => q + 1) 8 p) = p := by
  -- Rewrite the step as `(· + 1)` and use the general iterate lemma.
  change ((· + (1 : Phase))^[8]) p = p
  have h : ((· + (1 : Phase))^[8]) p = p + 8 • (1 : Phase) := by
    simpa using (add_right_iterate_apply (n := 8) (a := (1 : Phase)) (b := p))
  -- Discharge the RHS by computation in `Fin 8`.
  have h80 : (8 • (1 : Phase)) = (0 : Phase) := by
    decide
  calc
    ((· + (1 : Phase))^[8]) p = p + 8 • (1 : Phase) := h
    _ = p + (0 : Phase) := by simp [h80]
    _ = p := by simp

/-! ## Gray-cycle witness facts (period 8, adjacency, cover) -/

noncomputable abbrev patternAtPhase := OctaveKernel.Instances.patternAtPhase

theorem patternAtPhase_surjective : Function.Surjective patternAtPhase :=
  OctaveKernel.Instances.patternAtPhase_surjective

theorem patternAtPhase_oneBit_step (t : Phase) :
    Patterns.OneBitDiff (patternAtPhase t) (patternAtPhase (t + 1)) :=
  OctaveKernel.Instances.patternAtPhase_oneBit_step t

end
end Octave
end IndisputableMonolith
