import IndisputableMonolith.Foundation.RecognitionOperator
import IndisputableMonolith.Ethics.MoralState
import IndisputableMonolith.Ethics.ConservationLaw
import IndisputableMonolith.Ethics.Harm
import IndisputableMonolith.Ethics.LeastAction
import IndisputableMonolith.Constants
import IndisputableMonolith.Support.GoldenRatio

namespace IndisputableMonolith
namespace Ethics
namespace Virtues

open Foundation MoralState

/-! Courage provides action enablement for high-gradient states. -/

/-- Apply courage to a state list. -/
noncomputable def ApplyCourage (states : List MoralState) : List MoralState :=
  states

/-- Courage virtue definition. -/
noncomputable def courageVirtue : Virtue where
  transform := ApplyCourage
  conserves_reciprocity := fun states h => h  -- ApplyCourage is identity, preserves admissibility
  minimizes_local_J := fun _ => trivial
  respects_cadence := fun states h_coh s hs s' hs' => by
    -- ApplyCourage is identity, so states' = states
    -- Use time-coherence: any two states in the list have times within 8 ticks
    simp only [ApplyCourage] at hs'
    have := h_coh s hs s' hs'
    exact this.1
  gauge_invariant := fun _ => trivial

/-- **DEFINITION: Courageous Action**
    An action is courageous if it is internalized (no self-harm surcharge)
    relative to the performing agent. -/
def IsCourageous (i : AgentId) (action : Harm.ActionSpec) (s : LedgerState) : Prop :=
  Harm.InternalizedFor action i s

/-- **THEOREM (PROVED)**: Courageous actions incur no self-harm surcharge.
    Proof: Courageous actions are internalized by definition, and internalized
    actions have zero self-harm (proven in Harm.lean). -/
theorem courage_self_harm_zero (i : AgentId) (action : Harm.ActionSpec) (baseline : LedgerState)
    (h_agent : action.agent = i) (h_courage : IsCourageous i action baseline) :
    Harm.harm i i action baseline h_agent = 0 :=
  Harm.harm_self_zero_of_internalized i action baseline h_agent h_courage

/-- Harm matrix instantiated for a courageous action over an admissible baseline. -/
noncomputable def courage_harm_matrix
  (agents : List AgentId)
  (spec : Harm.ActionSpec)
  (baseline : LedgerState)
  (h_balanced : Foundation.reciprocity_skew_abs baseline = 0)
  (h_courage : IsCourageous spec.agent spec baseline) : Harm.HarmMatrix :=
  Harm.compute_harm_matrix agents spec baseline h_balanced ⟨rfl, courage_self_harm_zero _ _ _ rfl h_courage⟩

lemma courage_harm_nonneg
  (agents : List AgentId)
  (spec : Harm.ActionSpec)
  (baseline : LedgerState)
  (h_balanced : Foundation.reciprocity_skew_abs baseline = 0)
  (h_courage : IsCourageous spec.agent spec baseline)
  (i j : AgentId) (h_neq : i ≠ j) :
  0 ≤ (courage_harm_matrix agents spec baseline h_balanced h_courage).harm_values i j :=
  (courage_harm_matrix agents spec baseline h_balanced h_courage).nonneg i j h_neq

lemma courage_harm_self_zero
  (agents : List AgentId)
  (spec : Harm.ActionSpec)
  (baseline : LedgerState)
  (h_balanced : Foundation.reciprocity_skew_abs baseline = 0)
  (h_courage : IsCourageous spec.agent spec baseline)
  (i : AgentId) :
  (courage_harm_matrix agents spec baseline h_balanced h_courage).harm_values i i = 0 :=
  (courage_harm_matrix agents spec baseline h_balanced h_courage).self_zero i

end Virtues
end Ethics
end IndisputableMonolith
