import Mathlib
import IndisputableMonolith.Foundation.RecognitionOperator
import IndisputableMonolith.Cost
import IndisputableMonolith.Ethics.MoralState
import IndisputableMonolith.Ethics.ConservationLaw
import IndisputableMonolith.Ethics.Consent

namespace IndisputableMonolith.Ethics.Harm

open Foundation Classical Cost

/-! # Harm (ΔS): Externalized Action Surcharge -/

/-- Bond-level log-strain update. -/
structure ActionSpec where
  agent : AgentId
  support : Finset BondId
  logStrain : BondId → ℝ
  logStrain_zero_of_not_mem : ∀ {b}, b ∉ support → logStrain b = 0

/-- Scaling factor induced by log-strain: x' = x * exp(v). -/
noncomputable def ActionSpec.factor (action : ActionSpec) (b : BondId) : ℝ :=
  Real.exp (action.logStrain b)

/-- Total log-strain applied by an action (sum over support). -/
noncomputable def ActionSpec.totalLogStrain (action : ActionSpec) : ℝ :=
  action.support.sum action.logStrain

def ActionSpec.sigmaBalanced (action : ActionSpec) : Prop :=
  action.totalLogStrain = 0

/-- Filter active bonds by agent ownership. -/
noncomputable def bondsOfAgent (s : LedgerState) (j : AgentId) : Finset BondId :=
  s.active_bonds.filter (fun b =>
    match s.bond_agents b with
    | some (a1, a2) => a1 = j ∨ a2 = j
    | none => false
  )

noncomputable def agentCost (s : LedgerState) (j : AgentId) : ℝ :=
  (bondsOfAgent s j).sum (fun b => Jcost (s.bond_multipliers b))

/-- Apply an action to a ledger state. -/
noncomputable def apply_action (action : ActionSpec) (s : LedgerState) : LedgerState := {
  s with
  bond_multipliers := fun b => s.bond_multipliers b * action.factor b,
  bond_pos := fun {b} hb =>
    mul_pos (s.bond_pos hb) (Real.exp_pos (action.logStrain b))
}

/-- Harm is the difference in agent cost between the action and the neutral baseline. -/
noncomputable def harm (i j : AgentId) (action : ActionSpec) (baseline : LedgerState)
  (_h_agent : action.agent = i) : ℝ :=
  let next_state := apply_action action baseline
  agentCost next_state j - agentCost baseline j

/-- Harm is non-negative when calculated against a perfectly balanced baseline (σ_abs = 0). -/
theorem harm_nonneg (i j : AgentId) (action : ActionSpec) (baseline : LedgerState)
  (_h_agent : action.agent = i) (h_balanced : Foundation.reciprocity_skew_abs baseline = 0) :
  0 ≤ harm i j action baseline _h_agent := by
  simp only [harm]
  -- Since baseline is perfectly balanced, all multipliers are 1.
  have h1 : ∀ b ∈ baseline.active_bonds, baseline.bond_multipliers b = 1 := by
    rw [IndisputableMonolith.Ethics.ConservationLaw.reciprocity_skew_abs_eq_zero_iff] at h_balanced
    exact h_balanced
  -- Then J(multipliers) = J(1) = 0.
  have h2 : ∀ b ∈ baseline.active_bonds, Jcost (baseline.bond_multipliers b) = 0 := by
    intro b hb
    rw [h1 b hb]
    exact Jcost_unit0
  -- So agentCost baseline j = 0.
  have h3 : agentCost baseline j = 0 := by
    unfold agentCost
    apply Finset.sum_eq_zero
    intro b hb
    apply h2
    unfold bondsOfAgent at hb
    exact (Finset.mem_filter.mp hb).1
  rw [h3, sub_zero]
  unfold agentCost
  apply Finset.sum_nonneg
  intro b hb
  unfold apply_action
  dsimp
  apply Jcost_nonneg
  apply (apply_action action baseline).bond_pos
  unfold bondsOfAgent at hb
  exact (Finset.mem_filter.mp hb).1

/-- An action is "internalized" for an agent if it only affects bonds not owned by that agent. -/
def InternalizedFor (action : ActionSpec) (i : AgentId) (s : LedgerState) : Prop :=
  ∀ b ∈ action.support, b ∉ bondsOfAgent s i

/-- **THEOREM (PROVED)**: Internalized actions incur no self-harm. -/
theorem harm_self_zero_of_internalized (i : AgentId) (action : ActionSpec) (baseline : LedgerState)
    (h_agent : action.agent = i) (h_int : InternalizedFor action i baseline) :
    harm i i action baseline h_agent = 0 := by
  simp only [harm]
  have h_cost : agentCost (apply_action action baseline) i = agentCost baseline i := by
    unfold agentCost bondsOfAgent apply_action
    dsimp
    apply Finset.sum_congr rfl
    intro b hb
    simp only [Finset.mem_filter] at hb
    have hb_not_supp : b ∉ action.support := fun h_supp =>
      h_int b h_supp (by
        simp only [bondsOfAgent, Finset.mem_filter]
        exact hb)
    unfold ActionSpec.factor
    rw [action.logStrain_zero_of_not_mem hb_not_supp, Real.exp_zero, mul_one]
  rw [h_cost, sub_self]

def harm_self_zero_hypothesis (i : AgentId) (action : ActionSpec) (baseline : LedgerState) : Prop :=
  ∃ h : action.agent = i, harm i i action baseline h = 0

structure HarmMatrix where
  harm_values : AgentId → AgentId → ℝ
  nonneg : ∀ i j, i ≠ j → 0 ≤ harm_values i j
  self_zero : ∀ i, harm_values i i = 0

/-- Compute the harm matrix for a set of agents. -/
noncomputable def compute_harm_matrix
  (_agents : List AgentId) (action : ActionSpec) (baseline : LedgerState)
  (h_bal : Foundation.reciprocity_skew_abs baseline = 0)
  (h_self_zero : harm_self_zero_hypothesis action.agent action baseline) : HarmMatrix :=
  {
    harm_values := fun i j =>
      if h : action.agent = i then harm i j action baseline h else 0,
    nonneg := fun i j _ => by
      split_ifs with h_agent
      · exact harm_nonneg i j action baseline h_agent h_bal
      · exact le_refl 0,
    self_zero := fun i => by
      split_ifs with h_agent
      · -- We need to show harm i i ... = 0 given h_self_zero about action.agent
        rcases h_self_zero with ⟨h_orig, h_val⟩
        -- Substitute h_agent : action.agent = i
        subst h_agent
        -- Now both proofs h_agent and h_orig are of the same type (rfl)
        -- They're equal by proof irrelevance
        congr
      · rfl
  }

noncomputable def max_harm (matrix : HarmMatrix) (agents : List AgentId) : ℝ :=
  agents.foldl (fun acc i =>
    agents.foldl (fun inner j => max inner (matrix.harm_values i j)) acc) 0

/-- Aggregated harm across a target set. -/
noncomputable def harm_over (i : AgentId) (targets : Finset AgentId) (action : ActionSpec) (baseline : LedgerState) (h : action.agent = i) : ℝ :=
  targets.sum (fun j => harm i j action baseline h)

/-- Neutral action does nothing. -/
noncomputable def neutral_action (i : AgentId) : ActionSpec := {
  agent := i,
  support := ∅,
  logStrain := fun _ => 0,
  logStrain_zero_of_not_mem := fun _ => rfl
}

noncomputable def linBondDelta (x v : ℝ) : ℝ :=
  Jcost (x * Real.exp v) - Jcost x

noncomputable def remBondDelta (x v : ℝ) : ℝ :=
  linBondDelta x v

end IndisputableMonolith.Ethics.Harm
