import IndisputableMonolith.OctaveKernel.Bridges.LayerProjections

namespace IndisputableMonolith
namespace OctaveKernel
namespace Bridges

/-!
# OctaveKernel.Bridges.AlignmentTheorems

Small, reusable theorems that turn the `Bridge` structure into concrete
cross-layer alignment statements.

These are **structural** facts: they depend only on `preservesPhase` and
`commutesStep`, not on any empirical interpretation.
-/

/-! ## Generic: mapping preserves alignment -/

/-- If two states are aligned (same phase), then mapping them through bridges preserves alignment. -/
theorem aligned_map {L₁ L₂ L₁' L₂' : Layer}
    (B₁ : Bridge L₁ L₁') (B₂ : Bridge L₂ L₂')
    {s₁ : L₁.State} {s₂ : L₂.State} :
    Aligned L₁ L₂ s₁ s₂ → Aligned L₁' L₂' (B₁.map s₁) (B₂.map s₂) := by
  intro h
  unfold Aligned at *
  -- Push alignment through phase-preservation on both sides.
  simpa [B₁.preservesPhase s₁, B₂.preservesPhase s₂] using h

/-- If two states are aligned, then their bridge-images remain aligned after `n` steps. -/
theorem aligned_iterate_map {L₁ L₂ L₁' L₂' : Layer}
    (B₁ : Bridge L₁ L₁') (B₂ : Bridge L₂ L₂')
    (hAdv₁' : Layer.StepAdvances L₁') (hAdv₂' : Layer.StepAdvances L₂') :
    ∀ n (s₁ : L₁.State) (s₂ : L₂.State),
      Aligned L₁ L₂ s₁ s₂ →
        Aligned L₁' L₂'
          (Function.iterate L₁'.step n (B₁.map s₁))
          (Function.iterate L₂'.step n (B₂.map s₂)) := by
  intro n s₁ s₂ hAligned
  -- First move the initial alignment through the bridges...
  have h0 : Aligned L₁' L₂' (B₁.map s₁) (B₂.map s₂) :=
    aligned_map (B₁ := B₁) (B₂ := B₂) hAligned
  -- ...then use `StepAdvances` on the targets to propagate it through iteration.
  exact aligned_iterate (L₁ := L₁') (L₂ := L₂') hAdv₁' hAdv₂' n (B₁.map s₁) (B₂.map s₂) h0

/-! ## Concrete: Biology ↔ Consciousness alignment transported to WaterClock -/

/-- If Biology and Consciousness are phase-aligned initially, their WaterClock images stay aligned. -/
theorem biology_consciousness_aligned_water_iterate :
    ∀ n (sB : Instances.BiologyQualiaLayer.State) (sC : Instances.ConsciousnessPhaseLayer.State),
      Aligned Instances.BiologyQualiaLayer Instances.ConsciousnessPhaseLayer sB sC →
        Aligned Instances.WaterClockLayer Instances.WaterClockLayer
          (Function.iterate Instances.WaterClockLayer.step n (biologyToWaterClockBridge.map sB))
          (Function.iterate Instances.WaterClockLayer.step n (consciousnessToWaterClockBridge.map sC)) := by
  intro n sB sC h
  -- WaterClock is a StepAdvances layer, so once phases are aligned they stay aligned.
  exact aligned_iterate_map
    (B₁ := biologyToWaterClockBridge) (B₂ := consciousnessToWaterClockBridge)
    Instances.WaterClockLayer_stepAdvances Instances.WaterClockLayer_stepAdvances
    n sB sC h

/-! ## Concrete: MeaningNote ↔ Biology alignment transported to WaterClock -/

/-- If MeaningNote and Biology are phase-aligned initially, their WaterClock images stay aligned. -/
theorem meaningNote_biology_aligned_water_iterate :
    ∀ n (sN : Instances.MeaningNoteLayer.State) (sB : Instances.BiologyQualiaLayer.State),
      Aligned Instances.MeaningNoteLayer Instances.BiologyQualiaLayer sN sB →
        Aligned Instances.WaterClockLayer Instances.WaterClockLayer
          (Function.iterate Instances.WaterClockLayer.step n (meaningNoteToWaterClockBridge.map sN))
          (Function.iterate Instances.WaterClockLayer.step n (biologyToWaterClockBridge.map sB)) := by
  intro n sN sB h
  exact aligned_iterate_map
    (B₁ := meaningNoteToWaterClockBridge) (B₂ := biologyToWaterClockBridge)
    Instances.WaterClockLayer_stepAdvances Instances.WaterClockLayer_stepAdvances
    n sN sB h

/-! ## Concrete: MeaningNote ↔ LNAL alignment transported to WaterClock -/

/-- If MeaningNote and LNAL are phase-aligned initially, their WaterClock images stay aligned. -/
theorem meaningNote_lnal_aligned_water_iterate (P : LNAL.LProgram) :
    ∀ n (sN : Instances.MeaningNoteLayer.State) (sL : (Instances.LNALBreathLayer P).State),
      Aligned Instances.MeaningNoteLayer (Instances.LNALBreathLayer P) sN sL →
        Aligned Instances.WaterClockLayer Instances.WaterClockLayer
          (Function.iterate Instances.WaterClockLayer.step n (meaningNoteToWaterClockBridge.map sN))
          (Function.iterate Instances.WaterClockLayer.step n ((lnalToWaterClockBridge P).map sL)) := by
  intro n sN sL h
  exact aligned_iterate_map
    (B₁ := meaningNoteToWaterClockBridge) (B₂ := lnalToWaterClockBridge P)
    Instances.WaterClockLayer_stepAdvances Instances.WaterClockLayer_stepAdvances
    n sN sL h

/-! ## Concrete: MeaningNote ↔ Consciousness alignment transported to WaterClock -/

/-- If MeaningNote and Consciousness are phase-aligned initially, their WaterClock images stay aligned. -/
theorem meaningNote_consciousness_aligned_water_iterate :
    ∀ n (sN : Instances.MeaningNoteLayer.State) (sC : Instances.ConsciousnessPhaseLayer.State),
      Aligned Instances.MeaningNoteLayer Instances.ConsciousnessPhaseLayer sN sC →
        Aligned Instances.WaterClockLayer Instances.WaterClockLayer
          (Function.iterate Instances.WaterClockLayer.step n (meaningNoteToWaterClockBridge.map sN))
          (Function.iterate Instances.WaterClockLayer.step n (consciousnessToWaterClockBridge.map sC)) := by
  intro n sN sC h
  exact aligned_iterate_map
    (B₁ := meaningNoteToWaterClockBridge) (B₂ := consciousnessToWaterClockBridge)
    Instances.WaterClockLayer_stepAdvances Instances.WaterClockLayer_stepAdvances
    n sN sC h

/-! ## Cross-layer cost comparison theorems -/

/-- If a layer has NonincreasingCost and all states are admissible, cost decreases over iteration. -/
theorem cost_nonincreasing_iterate {L : Layer}
    (hCost : L.NonincreasingCost)
    (hAdm : ∀ s, L.admissible s) :
    ∀ n s, L.cost (Function.iterate L.step n s) ≤ L.cost s := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
    intro s
    have hStep : Function.iterate L.step (n + 1) s = L.step (Function.iterate L.step n s) :=
      Function.iterate_succ_apply' L.step n s
    rw [hStep]
    have h1 : L.cost (L.step (Function.iterate L.step n s)) ≤ L.cost (Function.iterate L.step n s) :=
      hCost (Function.iterate L.step n s) (hAdm _)
    have h2 : L.cost (Function.iterate L.step n s) ≤ L.cost s := ih s
    exact le_trans h1 h2

/-- When two phase-aligned layers both have NonincreasingCost, their costs both decrease in lockstep. -/
theorem aligned_costs_both_decrease {L₁ L₂ : Layer}
    (hCost₁ : L₁.NonincreasingCost) (hCost₂ : L₂.NonincreasingCost)
    (hAdm₁ : ∀ s, L₁.admissible s) (hAdm₂ : ∀ s, L₂.admissible s)
    (hAdv₁ : L₁.StepAdvances) (hAdv₂ : L₂.StepAdvances)
    {s₁ : L₁.State} {s₂ : L₂.State}
    (hAligned : Aligned L₁ L₂ s₁ s₂) :
    ∀ n, L₁.cost (Function.iterate L₁.step n s₁) ≤ L₁.cost s₁ ∧
         L₂.cost (Function.iterate L₂.step n s₂) ≤ L₂.cost s₂ ∧
         Aligned L₁ L₂ (Function.iterate L₁.step n s₁) (Function.iterate L₂.step n s₂) := by
  intro n
  constructor
  · exact cost_nonincreasing_iterate hCost₁ hAdm₁ n s₁
  constructor
  · exact cost_nonincreasing_iterate hCost₂ hAdm₂ n s₂
  · exact aligned_iterate hAdv₁ hAdv₂ n s₁ s₂ hAligned

/-- Concrete example: PatternCover and PhysicsScale costs both decrease while staying aligned.
    (Both have admissible := True, so the theorem applies directly.) -/
theorem patternCover_physics_costs_decrease :
    ∀ n (sP : Instances.PatternCoverLayer.State) (sPh : Instances.PhysicsScaleLayer.State),
      Aligned Instances.PatternCoverLayer Instances.PhysicsScaleLayer sP sPh →
        (Instances.PatternCoverLayer.cost
          (Function.iterate Instances.PatternCoverLayer.step n sP)
          ≤ Instances.PatternCoverLayer.cost sP) ∧
        (Instances.PhysicsScaleLayer.cost
          (Function.iterate Instances.PhysicsScaleLayer.step n sPh)
          ≤ Instances.PhysicsScaleLayer.cost sPh) ∧
        Aligned Instances.PatternCoverLayer Instances.PhysicsScaleLayer
          (Function.iterate Instances.PatternCoverLayer.step n sP)
          (Function.iterate Instances.PhysicsScaleLayer.step n sPh) := by
  intro n sP sPh hAligned
  exact aligned_costs_both_decrease
    Instances.PatternCoverLayer_nonincreasingCost
    Instances.PhysicsScaleLayer_nonincreasingCost
    (fun _ => trivial)  -- PatternCoverLayer.admissible = True
    (fun _ => trivial)  -- PhysicsScaleLayer.admissible = True
    Instances.PatternCoverLayer_stepAdvances
    Instances.PhysicsScaleLayer_stepAdvances
    hAligned n

end Bridges
end OctaveKernel
end IndisputableMonolith
