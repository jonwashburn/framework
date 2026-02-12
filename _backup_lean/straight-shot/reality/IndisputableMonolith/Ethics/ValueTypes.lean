import Mathlib
import IndisputableMonolith.Foundation.RecognitionOperator

/-!
# Value Types (lightweight)

Minimal types needed by Ethics modules without pulling heavy analysis imports.

Provides:
- `AgentEnvDistribution`: coarse-grained agent–environment distribution
- `BondConfig`: active bond configuration with positive multipliers
- `unit_config`: empty configuration at unity
-/

namespace IndisputableMonolith
namespace Ethics
namespace ValueTypes

open Foundation

/-- Agent–environment joint distribution (coarse-grained ledger state). -/
structure AgentEnvDistribution where
  /-- Agent states (finite partition). -/
  agent_states : Finset ℕ
  /-- Environment states (finite partition). -/
  env_states : Finset ℕ
  /-- Joint probability mass function (not normalized here beyond the proof). -/
  prob : ℕ → ℕ → ℝ
  /-- Probabilities are non-negative. -/
  prob_nonneg : ∀ a e, 0 ≤ prob a e
  /-- Probabilities sum to 1. -/
  prob_normalized : (agent_states.sum fun a => env_states.sum fun e => prob a e) = 1

/-- Bond configuration (finite active bonds with positive multipliers). -/
@[ext]
structure BondConfig where
  /-- Finite active bond set to be considered in the mechanical term. -/
  support : Finset BondId
  /-- Multiplier for each bond (only values on `support` are relevant). -/
  multiplier : BondId → ℝ
  /-- Positivity on the active set. -/
  multiplier_pos : ∀ {b}, b ∈ support → 0 < multiplier b

/-- The unit configuration with empty active set. -/
def unit_config : BondConfig where
  support := (∅ : Finset BondId)
  multiplier := fun _ => 1
  multiplier_pos := by
    intro b hb
    simpa using hb

end ValueTypes
end Ethics
end IndisputableMonolith
