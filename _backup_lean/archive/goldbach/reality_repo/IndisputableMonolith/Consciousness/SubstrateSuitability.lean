import Mathlib
import IndisputableMonolith.Foundation.RecognitionOperator
import IndisputableMonolith.Consciousness.ConsciousnessHamiltonian
import IndisputableMonolith.Consciousness.LightMemory

/-!
# Substrate Suitability and Reformation Cost
-/

namespace IndisputableMonolith.Consciousness

open Foundation

/-- φ-ladder distance between target rung and substrate rung. -/
def ladderDistance (target_rung substrate_rung : ℤ) : ℝ :=
  |(target_rung - substrate_rung : ℤ)|

/-- Suitability predicate: address match, channels available, complexity fit. -/
structure Substrate where
  boundary : StableBoundary
  rung : ℤ
  channels : ℕ

structure Suitability where
  address_match : Bool
  channels_sufficient : Bool
  complexity_ok : Bool

/-- Predicate: substrate is suitable for reformation of pattern. -/
def suitable (lm : LightMemoryState) (s : Substrate) : Prop :=
  let target_rung := lm.pattern.Z_invariant  -- simple address schema
  let d := ladderDistance target_rung s.rung
  (d ≤ 2) ∧ (s.channels ≥ lm.pattern.complexity) ∧ True

/-/ Reformation cost modeled via J at substrate scale (always finite real). -/
def reformationCost (lm : LightMemoryState) (s : Substrate) : ℝ :=
  let r := s.boundary.extent / λ_rec
  s.boundary.coherence_time * J r

lemma reformation_cost_form (lm : LightMemoryState) (s : Substrate) :
    reformationCost lm s = s.boundary.coherence_time * J (s.boundary.extent / λ_rec) := rfl

end IndisputableMonolith.Consciousness
