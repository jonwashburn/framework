import Mathlib
import IndisputableMonolith.Foundation.RecognitionOperator
import IndisputableMonolith.Ethics.MoralState
import IndisputableMonolith.Ethics.ConservationLaw
import IndisputableMonolith.Cost.JcostCore
import IndisputableMonolith.Ethics.LeastAction
import IndisputableMonolith.Ethics.Consent

/-!
# Harm (ΔS): Externalized Action Surcharge

This module implements the harm calculus from Section 4 of
`Morality-As-Conservation-Law.tex`.  Starting from an admissible baseline ledger
(σ = 0) and a finite action specification for an agent, we compute the required
post-projection action for each target agent and thus the externalized surcharge
```
ΔS(i → j) = Sⱼ*[α] − Sⱼ*[1].
```

We establish the main structural properties demanded in the paper:
* non-negativity on admissible baselines,
* additivity across independent targets,
* compositionality for disjoint action scopes,
* invariance under bond relabelings (discrete gauge symmetry),
* virtue-aligned corollaries (Love symmetry, Forgiveness and Sacrifice transfer).

The construction remains zero-parameter: no new tunable constants appear.
-/

namespace IndisputableMonolith
namespace Ethics
namespace Harm

open Foundation
open MoralState
open Cost (Jcost)
open scoped BigOperators Classical

/-! ## Action specifications -/

/--
`ActionSpec` stores a finite log-space strain imposed by an agent.  On each bond
inside `support` we add the logarithmic strain `logStrain`.  Outside the support
no strain is applied.
-/
structure ActionSpec where
  agent : AgentId
  support : Finset BondId
  logStrain : BondId → ℝ
  logStrain_zero_of_not_mem : ∀ ⦃b⦄, b ∉ support → logStrain b = 0

def ActionSpec.factor (action : ActionSpec) (b : BondId) : ℝ :=
  if h : b ∈ action.support then Real.exp (action.logStrain b) else 1

lemma factor_pos (action : ActionSpec) (b : BondId) :
    0 < action.factor b := by
  classical
  unfold ActionSpec.factor
  split_ifs with h
  · exact Real.exp_pos _
  · exact zero_lt_one

@[simp] lemma factor_eq_one_of_not_mem (action : ActionSpec)
    {b : BondId} (hb : b ∉ action.support) : action.factor b = 1 := by
  classical
  simp [ActionSpec.factor, hb]

@[simp] lemma factor_eq_exp_of_mem (action : ActionSpec)
    {b : BondId} (hb : b ∈ action.support) :
    action.factor b = Real.exp (action.logStrain b) := by
  classical
  simp [ActionSpec.factor, hb]

@[simp] lemma logStrain_of_not_mem (action : ActionSpec)
    {b : BondId} (hb : b ∉ action.support) : action.logStrain b = 0 :=
  action.logStrain_zero_of_not_mem hb

@[simp] lemma support_sum_logStrain_eq_sum (action : ActionSpec) :
    action.support.sum (fun b => action.logStrain b)
      = action.support.sum action.logStrain := rfl

/-- Total log-strain applied by an action (sum over support). -/
noncomputable def ActionSpec.totalLogStrain (action : ActionSpec) : ℝ :=
  action.support.sum action.logStrain

/-- σ=0 witness: the action keeps log-strain balanced when the total is 0. -/
def ActionSpec.sigmaBalanced (action : ActionSpec) : Prop :=
  action.totalLogStrain = 0

namespace ActionSpec

lemma totalLogStrain_eq_sum (action : ActionSpec) :
    action.totalLogStrain = action.support.sum action.logStrain := rfl

lemma totalLogStrain_zero_of_subsupport
  (action : ActionSpec) {b : BondId} (hb : b ∉ action.support) :
  action.logStrain b = 0 := action.logStrain_of_not_mem hb

/-- Construct the consent-direction tangent corresponding to an action with σ-balanced log strain. -/
noncomputable def directionSpecOfAction
  (action : ActionSpec)
  (h_sigma : action.sigmaBalanced) : Consent.DirectionSpec :=
  Consent.DirectionSpec.ofBondTangent
    action.agent
    action.support
    action.logStrain
    (by
      intro b hb
      exact action.logStrain_zero_of_not_mem hb)
    (by
      simpa [ActionSpec.sigmaBalanced, ActionSpec.totalLogStrain_eq_sum] using h_sigma)

@[simp]
lemma directionSpecOfAction_agent (action : ActionSpec)
  (h_sigma : action.sigmaBalanced) :
  (directionSpecOfAction action h_sigma).direction.agent = action.agent := rfl

@[simp]
lemma directionSpecOfAction_support (action : ActionSpec)
  (h_sigma : action.sigmaBalanced) :
  (directionSpecOfAction action h_sigma).support = action.support := rfl

lemma directionSpecOfAction_direction (action : ActionSpec)
  (h_sigma : action.sigmaBalanced) (b : BondId) :
  (directionSpecOfAction action h_sigma).direction.direction b = action.logStrain b := rfl

lemma directionSpecOfAction_prob_support (action : ActionSpec)
  (h_sigma : action.sigmaBalanced) :
  (directionSpecOfAction action h_sigma).prob_support = ∅ := rfl

end ActionSpec

/-- Neutral action: empty support, zero strain. -/
noncomputable def neutral (agent : AgentId) : ActionSpec :=
  { agent := agent
    support := ∅
    logStrain := fun _ => 0
    logStrain_zero_of_not_mem := by
      intro b hb; simpa using hb }

/-- Backwards-compatible name for the neutral action. -/
noncomputable def neutral_action (agent : AgentId) : ActionSpec := neutral agent

@[simp] lemma neutral_action_eq (agent : AgentId) : neutral_action agent = neutral agent := rfl

@[simp] lemma neutral_support (agent : AgentId) :
    (neutral agent).support = (∅ : Finset BondId) := rfl

@[simp] lemma neutral_factor (agent : AgentId) (b : BondId) :
    (neutral agent).factor b = 1 := by
  classical
  simp [neutral, ActionSpec.factor]

/-! ## Applying an action to a ledger -/

/-- Apply an action by scaling the baseline multipliers on the support. -/
noncomputable def applyAction (action : ActionSpec) (baseline : LedgerState) : LedgerState :=
{ baseline with
  bond_multipliers := fun b => baseline.bond_multipliers b * action.factor b
, bond_pos := by
    intro b hb
    have hb_pos := baseline.bond_pos hb
    have hf_pos := factor_pos action b
    simpa [applyAction, ActionSpec.factor] using mul_pos hb_pos hf_pos }

@[simp]
lemma applyAction_active (action : ActionSpec) (baseline : LedgerState) :
    (applyAction action baseline).active_bonds = baseline.active_bonds := rfl

@[simp]
lemma applyAction_bond_agents (action : ActionSpec) (baseline : LedgerState) (b : BondId) :
    (applyAction action baseline).bond_agents b = baseline.bond_agents b := rfl

@[simp]
lemma applyAction_factor (action : ActionSpec) (baseline : LedgerState) (b : BondId) :
    (applyAction action baseline).bond_multipliers b =
      baseline.bond_multipliers b * action.factor b := rfl

@[simp]
lemma applyAction_neutral (baseline : LedgerState) (agent : AgentId) :
    applyAction (neutral agent) baseline = baseline := by
  classical
  ext b <;> simp [applyAction, neutral, ActionSpec.factor]

@[simp]
lemma bondsOfAgent_apply (action : ActionSpec) (baseline : LedgerState)
    (agent : AgentId) :
    bondsOfAgent (applyAction action baseline) agent =
      bondsOfAgent baseline agent := by
  classical
  ext b; constructor
  · intro hb
    have hb_active := (Finset.mem_filter.mp hb).1
    have hb_cond := (Finset.mem_filter.mp hb).2
    simp [bondsOfAgent, applyAction_active, applyAction_bond_agents,
      hb_active, hb_cond]
  · intro hb
    have hb_active := (Finset.mem_filter.mp hb).1
    have hb_cond := (Finset.mem_filter.mp hb).2
    simp [bondsOfAgent, applyAction_active, applyAction_bond_agents,
      hb_active, hb_cond]

@[simp]
lemma bondsOfAgents_apply (action : ActionSpec) (baseline : LedgerState)
    (agents : Finset AgentId) :
    bondsOfAgents (applyAction action baseline) agents =
      bondsOfAgents baseline agents := by
  classical
  ext b; constructor
  · intro hb
    have hb_active := (Finset.mem_filter.mp hb).1
    have hb_cond := (Finset.mem_filter.mp hb).2
    simp [bondsOfAgents, applyAction_active, applyAction_bond_agents,
      hb_active, hb_cond]
  · intro hb
    have hb_active := (Finset.mem_filter.mp hb).1
    have hb_cond := (Finset.mem_filter.mp hb).2
    simp [bondsOfAgents, applyAction_active, applyAction_bond_agents,
      hb_active, hb_cond]

/-! ## Bond selections and partial costs -/

noncomputable def bondsOfAgent (s : LedgerState) (agent : AgentId) : Finset BondId :=
  s.active_bonds.filter (fun b =>
    match s.bond_agents b with
    | some (a₁, a₂) => a₁ = agent ∨ a₂ = agent
    | none => False)

noncomputable def bondsOfAgents (s : LedgerState) (agents : Finset AgentId) : Finset BondId :=
  s.active_bonds.filter (fun b =>
    match s.bond_agents b with
    | some (a₁, a₂) => a₁ ∈ agents ∨ a₂ ∈ agents
    | none => False)

lemma bondsOfAgent_subset (s : LedgerState) (agent : AgentId) :
    bondsOfAgent s agent ⊆ s.active_bonds := by
  intro b hb
  exact (Finset.mem_filter.mp hb).1

/-- Cost borne by a single agent in ledger `s`. -/
noncomputable def agentCost (s : LedgerState) (agent : AgentId) : ℝ :=
  ∑ b in bondsOfAgent s agent, J (s.bond_multipliers b)

/-- Cost borne collectively by a finite set of agents. -/
noncomputable def agentsCost (s : LedgerState) (agents : Finset AgentId) : ℝ :=
  ∑ b in bondsOfAgents s agents, J (s.bond_multipliers b)

/-- Aggregate log-strain variance over an action support. -/
noncomputable def action_variance (action : ActionSpec) : ℝ :=
  action.support.sum fun b => (action.logStrain b) ^ 2

/-- Target-specific log-strain variance for a baseline ledger. -/
noncomputable def harm_variance
    (action : ActionSpec) (baseline : LedgerState) (agent : AgentId) : ℝ :=
  (bondsOfAgent baseline agent).sum fun b => (action.logStrain b) ^ 2

lemma action_variance_nonneg (action : ActionSpec) :
    0 ≤ action_variance action := by
  classical
  unfold action_variance
  refine Finset.sum_nonneg ?_
  intro b hb
  exact sq_nonneg _

lemma harm_variance_nonneg
    (action : ActionSpec) (baseline : LedgerState) (agent : AgentId) :
    0 ≤ harm_variance action baseline agent := by
  classical
  unfold harm_variance
  refine Finset.sum_nonneg ?_
  intro b hb
  exact sq_nonneg _

/-! ## Required action and harm -/

noncomputable def required_action (agent : AgentId)
    (action : ActionSpec) (baseline : LedgerState) : ℝ :=
  agentCost (applyAction action baseline) agent

noncomputable def required_action_over (agents : Finset AgentId)
    (action : ActionSpec) (baseline : LedgerState) : ℝ :=
  agentsCost (applyAction action baseline) agents

noncomputable def harm (i j : AgentId) (action : ActionSpec)
    (baseline : LedgerState) (h_agent : action.agent = i) : ℝ :=
  required_action j action baseline -
    required_action j (neutral i) baseline

noncomputable def harm_over (i : AgentId) (targets : Finset AgentId)
    (action : ActionSpec) (baseline : LedgerState) (h_agent : action.agent = i) : ℝ :=
  required_action_over targets action baseline -
    required_action_over targets (neutral i) baseline

@[simp]
lemma harm_def (i j : AgentId) (action : ActionSpec) (baseline : LedgerState)
    (h_agent : action.agent = i) :
  harm i j action baseline h_agent =
    required_action j action baseline - required_action j (neutral i) baseline := rfl

/-! ### Per-bond contributions -/

def bondDelta (action : ActionSpec) (baseline : LedgerState) (b : BondId) : ℝ :=
  J (baseline.bond_multipliers b * action.factor b) - J (baseline.bond_multipliers b)

lemma harm_eq_sum_bondDelta
  (i j : AgentId) (action : ActionSpec) (baseline : LedgerState)
  (h_agent : action.agent = i) (h_admissible : Foundation.admissible baseline) :
  harm i j action baseline h_agent =
    ∑ b in bondsOfAgent baseline j, bondDelta action baseline b := by
  classical
  unfold harm bondDelta required_action agentCost
  have h_before := required_action_neutral_zero j baseline h_admissible
  simp [applyAction, Finset.sum_sub_distrib, h_before, mul_comm, mul_left_comm,
    mul_assoc]

/-- Represent a ledger as a value-functional BondConfig for mechanical terms. -/
noncomputable def bondConfigOf (s : LedgerState) : Consent.ValueTypes.BondConfig :=
{ support := s.active_bonds
, multiplier := s.bond_multipliers
, multiplier_pos := by
    intro b hb; exact s.bond_pos hb }

/-- Linearized per-bond delta for J under log-strain `L` at base `x`. -/
noncomputable def linBondDelta (x : ℝ) (L : ℝ) : ℝ := ((x - x⁻¹) / 2) * L

/-- Remainder after removing the linear term from the exact finite delta. -/
noncomputable def remBondDelta (x : ℝ) (L : ℝ) : ℝ :=
  J (x * Real.exp L) - J x - linBondDelta x L

/-- Per-bond decomposition: exact = linear + remainder. -/
lemma bondDelta_decompose (baseline : LedgerState) (action : ActionSpec) (b : BondId) :
  bondDelta action baseline b =
    linBondDelta (baseline.bond_multipliers b) (action.logStrain b)
    + remBondDelta (baseline.bond_multipliers b) (action.logStrain b) := by
  classical
  unfold bondDelta remBondDelta linBondDelta ActionSpec.factor
  by_cases hb : b ∈ action.support
  · simp [hb, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
  · simp [hb, sub_eq_add_neg]

/-- Mech contribution restricted to a set `S` under a direction spec. -/
noncomputable def mechContributionOn
  (x : Consent.ValueTypes.BondConfig) (S : Finset BondId)
  (spec : Consent.DirectionSpec) : ℝ :=
  S.sum (fun b => ((x.multiplier b - (x.multiplier b)⁻¹) / 2)
                    * spec.direction.direction b)

lemma mechContributionOn_subset_eq
  {x : Consent.ValueTypes.BondConfig} {S : Finset BondId}
  {spec : Consent.DirectionSpec}
  (hsub : spec.support ⊆ S) :
  mechContributionOn x S spec =
    mechContributionOn x spec.support spec := by
  classical
  unfold mechContributionOn
  have : S.filter (fun b => b ∈ spec.support) = spec.support := by
    ext b; constructor
    · intro hb
      have : b ∈ S ∧ b ∈ spec.support := Finset.mem_filter.mp hb
      exact this.2
    · intro hb
      refine Finset.mem_filter.mpr ?_
      exact ⟨hsub hb, hb⟩
  -- rewrite sum over S to sum over support via filtering zeros outside support
  have hzero : ∀ b ∉ spec.support, spec.direction.direction b = 0 := by
    intro b hb; exact spec.direction_zero_outside (b := b) hb
  have hrewrite : S.sum (fun b => ((x.multiplier b - (x.multiplier b)⁻¹) / 2)
                              * spec.direction.direction b)
      = (S.filter (fun b => b ∈ spec.support)).sum
          (fun b => ((x.multiplier b - (x.multiplier b)⁻¹) / 2)
                      * spec.direction.direction b) := by
    refine Finset.sum_subset_zero_on_of_pred _ ?_ ?_ ?_
    · exact fun b => b ∈ spec.support
    · intro b hbS hbnot
      have hb : b ∉ spec.support := by
        intro hbmem; exact hbnot hbmem
      simp [hzero b hb]
    · intro b hb hbmem; simp [hbmem]
    · intro b hb hbS hbmem; simp [hbmem]
  simp [hrewrite, this, mechContributionOn]

/-- For specs generated from an action, the restricted mech sum equals the linearized sum. -/
lemma mechContributionOn_eq_linSum_ofAction
  (baseline : LedgerState) (j : AgentId) (action : ActionSpec)
  (hσ : action.sigmaBalanced) :
  mechContributionOn (bondConfigOf baseline) (bondsOfAgent baseline j)
    (ActionSpec.directionSpecOfAction action hσ)
  = (bondsOfAgent baseline j).sum
      (fun b => linBondDelta (baseline.bond_multipliers b) (action.logStrain b)) := by
  classical
  unfold mechContributionOn linBondDelta ActionSpec.directionSpecOfAction bondConfigOf
  simp [ActionSpec.directionSpecOfAction_direction]

/-- ΔS decomposes into the linearized mech sum plus the per-bond remainder. -/
lemma harm_decompose_linear_plus_rem
  (i j : AgentId) (action : ActionSpec) (baseline : LedgerState)
  (h_agent : action.agent = i) (h_admissible : Foundation.admissible baseline) :
  harm i j action baseline h_agent =
    (bondsOfAgent baseline j).sum
      (fun b => linBondDelta (baseline.bond_multipliers b) (action.logStrain b))
    + (bondsOfAgent baseline j).sum
      (fun b => remBondDelta (baseline.bond_multipliers b) (action.logStrain b)) := by
  classical
  have hsum := harm_eq_sum_bondDelta i j action baseline h_agent h_admissible
  simp [hsum, Finset.sum_add_distrib, bondDelta_decompose]

/-- Bound the harm incurred by limiting each per-bond contribution. -/
lemma harm_le_card_mul_bound
  (i j : AgentId) (action : ActionSpec) (baseline : LedgerState)
  (h_agent : action.agent = i) (h_admissible : Foundation.admissible baseline)
  (bound : ℝ)
  (h_bound : ∀ b ∈ bondsOfAgent baseline j,
      bondDelta action baseline b ≤ bound) :
  harm i j action baseline h_agent ≤
    (bondsOfAgent baseline j).card * bound := by
  classical
  set S := bondsOfAgent baseline j with hS
  have h_repr := harm_eq_sum_bondDelta i j action baseline h_agent h_admissible
  have h_sum_le : (∑ b in S, bondDelta action baseline b) ≤ ∑ _b in S, bound := by
    refine Finset.sum_le_sum ?_
    intro b hb
    simpa [S] using h_bound b (by simpa [S] using hb)
  have h_const : ∑ _b in S, bound = (S.card : ℝ) * bound := by
    simpa [S, nsmul_eq_mul] using (Finset.sum_const (s := S) (b := bound))
  calc
    harm i j action baseline h_agent
        = ∑ b in S, bondDelta action baseline b := by simpa [S] using h_repr
    _ ≤ ∑ _b in S, bound := h_sum_le
    _ = (S.card : ℝ) * bound := h_const

lemma bondDelta_neutral (baseline : LedgerState) (b : BondId) (i : AgentId) :
  bondDelta (neutral i) baseline b = 0 := by
  classical
  unfold bondDelta
  simp

/-! ## Fundamental identities -/

lemma required_action_neutral_zero (j : AgentId) (baseline : LedgerState)
    (h_admissible : Foundation.admissible baseline) :
    required_action j (neutral j) baseline = 0 := by
  classical
  unfold required_action agentCost
  have hσ :=
    (ConservationLaw.reciprocity_skew_eq_zero_iff baseline).1 h_admissible
  have hvals :
      ∀ b ∈ bondsOfAgent baseline j, baseline.bond_multipliers b = 1 := by
    intro b hb
    exact hσ b (bondsOfAgent_subset baseline j hb)
  simp [applyAction_neutral, agentCost, hvals, J_zero_at_one]

/-- ΔS is non-negative on admissible baselines (σ = 0). -/
lemma harm_nonneg
  (i j : AgentId) (action : ActionSpec) (baseline : LedgerState)
  (h_agent : action.agent = i) (h_admissible : Foundation.admissible baseline) :
  0 ≤ harm i j action baseline h_agent := by
  classical
  unfold harm required_action agentCost
  have h_before := required_action_neutral_zero j baseline h_admissible
  have h_after_nonneg :
      0 ≤ ∑ b in bondsOfAgent (applyAction action baseline) j,
        J ((applyAction action baseline).bond_multipliers b) := by
    refine Finset.sum_nonneg ?_
    intro b hb
    exact ConservationLaw.J_nonneg _
      ((applyAction action baseline).bond_pos ((Finset.mem_filter.mp hb).1))
  have := sub_nonneg.mpr h_after_nonneg
  simpa [h_before]

/-! ### Additivity on independent targets -/

lemma bondsOfAgents_union
  (s : LedgerState) (j k : AgentId) :
  bondsOfAgents s ({j} ∪ {k}) = bondsOfAgent s j ∪ bondsOfAgent s k := by
  classical
  ext b; constructor
  · intro hb
    have hb_active := (Finset.mem_filter.mp hb).1
    have hb_cond := (Finset.mem_filter.mp hb).2
    cases hba : s.bond_agents b with
    | none => simpa [bondsOfAgents, hba] using hb
    | some p =>
        rcases p with ⟨a₁, a₂⟩
        have : a₁ = j ∨ a₂ = j ∨ a₁ = k ∨ a₂ = k := by
          simpa [bondsOfAgents, Finset.mem_filter, hb_active, hba,
            Finset.mem_union, Finset.mem_singleton] using hb_cond
        rcases this with h | h | h | h
        · left; simp [bondsOfAgent, Finset.mem_filter, hb_active, hba, h]
        · left; simp [bondsOfAgent, Finset.mem_filter, hb_active, hba, h]
        · right; simp [bondsOfAgent, Finset.mem_filter, hb_active, hba, h]
        · right; simp [bondsOfAgent, Finset.mem_filter, hb_active, hba, h]
  · intro hb
    have hb_active := by
      cases Finset.mem_union.mp hb with
      | inl hj => exact (Finset.mem_filter.mp hj).1
      | inr hk => exact (Finset.mem_filter.mp hk).1
    have hb_cond : (match s.bond_agents b with
        | some (a₁, a₂) => a₁ ∈ ({j} ∪ {k}) ∨ a₂ ∈ ({j} ∪ {k})
        | none => False) := by
      cases Finset.mem_union.mp hb with
      | inl hj =>
          have := (Finset.mem_filter.mp hj).2
          simpa [bondsOfAgent, Finset.mem_filter] using this
      | inr hk =>
          have := (Finset.mem_filter.mp hk).2
          simpa [bondsOfAgent, Finset.mem_filter, or_comm] using this
    cases hba : s.bond_agents b with
    | none => simpa [bondsOfAgents, hba]
    | some p =>
        rcases p with ⟨a₁, a₂⟩
        have : a₁ ∈ ({j} ∪ {k}) ∨ a₂ ∈ ({j} ∪ {k}) := hb_cond
        simpa [bondsOfAgents, Finset.mem_filter, hba, hb_active]

lemma harm_additive_on_independent_targets
  (i j k : AgentId) (action : ActionSpec) (baseline : LedgerState)
  (h_agent : action.agent = i)
  (h_disjoint : Disjoint (bondsOfAgent baseline j) (bondsOfAgent baseline k))
  (h_admissible : Foundation.admissible baseline) :
  harm_over i ({j} ∪ {k}) action baseline h_agent =
    harm i j action baseline h_agent + harm i k action baseline h_agent := by
  classical
  unfold harm_over harm required_action_over required_action agentCost agentsCost
  simp [bondsOfAgents_apply, bondsOfAgent_apply, bondsOfAgents_union,
    bondsOfAgent_subset, h_disjoint, required_action_neutral_zero,
    h_admissible, applyAction_neutral, Finset.sum_union] -- sums split cleanly

/-! ### Compositionality for disjoint scopes -/

noncomputable def combineDisjoint (a₁ a₂ : ActionSpec)
    (h_disjoint : Disjoint a₁.support a₂.support) : ActionSpec :=
{ agent := a₁.agent
  support := a₁.support ∪ a₂.support
  logStrain := fun b =>
    if h₁ : b ∈ a₁.support then a₁.logStrain b
    else if h₂ : b ∈ a₂.support then a₂.logStrain b else 0
  logStrain_zero_of_not_mem := by
    intro b hb
    classical
    by_cases h₁ : b ∈ a₁.support
    · exact False.elim (hb (Finset.mem_union.mpr <| Or.inl h₁))
    · by_cases h₂ : b ∈ a₂.support
      · exact False.elim (hb (Finset.mem_union.mpr <| Or.inr h₂))
      · simp [h₁, h₂]
}

lemma combineDisjoint_factor (a₁ a₂ : ActionSpec)
    (h_disjoint : Disjoint a₁.support a₂.support) (b : BondId) :
  (combineDisjoint a₁ a₂ h_disjoint).factor b =
    if h₁ : b ∈ a₁.support then a₁.factor b
    else if h₂ : b ∈ a₂.support then a₂.factor b else 1 := by
  classical
  unfold combineDisjoint ActionSpec.factor
  split_ifs with h₁ h₂
  · simp [h₁]
  · have : b ∉ a₁.support := by
      intro hb; exact (Finset.disjoint_left.mp h_disjoint) hb h₂
    simp [h₁, h₂, this]
  · have : b ∉ a₁.support := by
      intro hb; exact (Finset.disjoint_right.mp h_disjoint) hb h₁
    simp [h₁, h₂, this]
  · simp

lemma harm_compositional_disjoint_scopes
  (i j : AgentId) (a₁ a₂ : ActionSpec) (baseline : LedgerState)
  (h_agent₁ : a₁.agent = i) (h_agent₂ : a₂.agent = i)
  (h_disjoint : Disjoint a₁.support a₂.support)
  (h_admissible : Foundation.admissible baseline) :
  harm i j (combineDisjoint a₁ a₂ h_disjoint) baseline rfl =
    harm i j a₁ baseline h_agent₁ + harm i j a₂ baseline h_agent₂ := by
  classical
  have hsum := harm_eq_sum_bondDelta i j (combineDisjoint a₁ a₂ h_disjoint)
    baseline rfl h_admissible
  have hsum₁ := harm_eq_sum_bondDelta i j a₁ baseline h_agent₁ h_admissible
  have hsum₂ := harm_eq_sum_bondDelta i j a₂ baseline h_agent₂ h_admissible
  have hbonds := bondsOfAgent baseline j
  have hbDelta : ∀ b ∈ hbonds,
      bondDelta (combineDisjoint a₁ a₂ h_disjoint) baseline b =
        bondDelta a₁ baseline b + bondDelta a₂ baseline b := by
    intro b hb
    unfold bondDelta combineDisjoint_factor combineDisjoint
    classical
    by_cases h₁ : b ∈ a₁.support
    · have h₂ : b ∉ a₂.support := by
        intro hb2
        exact (Finset.disjoint_left.mp h_disjoint) h₁ hb2
      simp [h₁, h₂, ActionSpec.factor_eq_one_of_not_mem, logStrain_of_not_mem]
    · by_cases h₂ : b ∈ a₂.support
      · have h₁' : b ∉ a₁.support := by
          intro hb1
          exact (Finset.disjoint_left.mp h_disjoint.symm) h₂ hb1
        simp [h₁, h₂, h₁', ActionSpec.factor_eq_one_of_not_mem, logStrain_of_not_mem]
      · simp [h₁, h₂]
  simp [hsum, hsum₁, hsum₂, hbDelta, Finset.sum_add_distrib]

/-! ### Harm vanishes when the target's bonds are untouched -/

lemma harm_zero_of_support_disjoint
  (i j : AgentId) (action : ActionSpec) (baseline : LedgerState)
  (h_agent : action.agent = i)
  (h_disjoint : Disjoint action.support (bondsOfAgent baseline j))
  (h_admissible : Foundation.admissible baseline) :
  harm i j action baseline h_agent = 0 := by
  classical
  unfold harm required_action agentCost
  have h_before := required_action_neutral_zero j baseline h_admissible
  have hzero :
      ∀ b ∈ bondsOfAgent baseline j, (applyAction action baseline).bond_multipliers b = 1 := by
    intro b hb
    have hb_active := bondsOfAgent_subset baseline j hb
    have hb_support : b ∉ action.support := by
      exact Finset.disjoint_left.mp h_disjoint hb
    simp [applyAction_factor, hb_support,
      (ConservationLaw.reciprocity_skew_eq_zero_iff baseline).1 h_admissible _ hb_active]
  simp [applyAction, hzero, h_before, agentCost]

/-! ## Gauge invariance (bond relabeling) -/

/-- Relabel a ledger by permuting bond identifiers. -/
noncomputable def permuteLedger (π : Equiv.Perm BondId) (s : LedgerState) : LedgerState :=
{ channels := s.channels
  , Z_patterns := s.Z_patterns
  , global_phase := s.global_phase
  , time := s.time
  , active_bonds := Finset.map (Function.Embedding.ofEquiv π) s.active_bonds
  , bond_multipliers := fun b => s.bond_multipliers (π.symm b)
  , bond_pos := by
      intro b hb
      obtain ⟨b', hb', rfl⟩ := Finset.mem_map.mp hb
      simpa using s.bond_pos hb'
  , bond_agents := fun b => s.bond_agents (π.symm b) }

/-- Relabel an action by permuting bond identifiers. -/
noncomputable def permuteAction (π : Equiv.Perm BondId) (action : ActionSpec) : ActionSpec :=
{ agent := action.agent
  , support := Finset.map (Function.Embedding.ofEquiv π) action.support
  , logStrain := fun b => action.logStrain (π.symm b)
  , logStrain_zero_of_not_mem := by
      intro b hb
      classical
      have hb' : π.symm b ∉ action.support := by
        intro h
        have : b ∈ Finset.map (Function.Embedding.ofEquiv π) action.support :=
          by
            refine ⟨π.symm b, h, ?_⟩
            simp
        exact hb this
      simpa [permuteAction] using action.logStrain_zero_of_not_mem hb' }

lemma permuteAction_factor (π : Equiv.Perm BondId) (action : ActionSpec) (b : BondId) :
    (permuteAction π action).factor b = action.factor (π.symm b) := by
  classical
  unfold permuteAction ActionSpec.factor
  split_ifs with h
  · obtain ⟨b', hb', rfl⟩ := Finset.mem_map.mp h
    simp [ActionSpec.factor] at hb'
    simpa [hb'.1, ActionSpec.factor]
  · simp [ActionSpec.factor]

@[simp]
lemma applyAction_permute
  (π : Equiv.Perm BondId) (action : ActionSpec) (baseline : LedgerState) :
  permuteLedger π (applyAction action baseline) =
    applyAction (permuteAction π action) (permuteLedger π baseline) := by
  classical
  ext b <;> simp [permuteLedger, permuteAction_factor, applyAction]

lemma bondsOfAgent_permute (π : Equiv.Perm BondId)
  (s : LedgerState) (agent : AgentId) :
  bondsOfAgent (permuteLedger π s) agent =
    Finset.map (Function.Embedding.ofEquiv π) (bondsOfAgent s agent) := by
  classical
  ext b; constructor
  · intro hb
    obtain ⟨b', hb', rfl⟩ := Finset.mem_map.mp hb
    exact ⟨b', hb', rfl⟩
  · intro hb
    obtain ⟨b', hb', rfl⟩ := hb
    simp [permuteLedger, bondsOfAgent] at hb'
    exact hb'

/-- Harm is invariant under bond relabeling (discrete gauge symmetry). -/
lemma harm_gauge_invariant
  (π : Equiv.Perm BondId) (i j : AgentId)
  (action : ActionSpec) (baseline : LedgerState)
  (h_agent : action.agent = i) :
  harm i j action baseline h_agent =
    harm i j (permuteAction π action)
      (permuteLedger π baseline) h_agent := by
  classical
  unfold harm required_action agentCost
  have := applyAction_permute π action baseline
  simp [this, bondsOfAgent_permute] -- permutations merely reindex the sums

/-! ### Consent compatibility -/

open Consent

lemma no_consent_of_negative_derivative
  (i j : AgentId)
  (spec : Consent.DirectionSpec)
  (p : Consent.ValueTypes.AgentEnvDistribution)
  (x : Consent.ValueTypes.BondConfig)
  (κ : ℝ) (h_κ : 0 < κ)
  (h_agent : spec.direction.agent = j)
  (h_prob_mem : ∀ pair ∈ spec.prob_support,
      pair.1 ∈ p.agent_states ∧ pair.2 ∈ p.env_states)
  (h_prob_pos : ∀ pair ∈ spec.prob_support, 0 < p.prob pair.1 pair.2)
  (h_support_mem : ∀ b ∈ spec.support, b ∈ x.support)
  (h_der : directional_derivative_value i j spec p x κ h_κ h_agent h_prob_mem h_prob_pos h_support_mem < 0) :
  ¬consent i j spec p x κ h_κ h_agent h_prob_mem h_prob_pos h_support_mem :=
  not_consent_of_derivative_neg i j spec p x κ h_κ h_agent h_prob_mem h_prob_pos h_support_mem h_der

lemma consent_violation_of_positive_harm
  (i j : AgentId)
  (action : ActionSpec)
  (baseline : LedgerState)
  (κ : ℝ) (h_κ : 0 < κ)
  (p : Consent.ValueTypes.AgentEnvDistribution)
  (x : Consent.ValueTypes.BondConfig)
  (spec : Consent.DirectionSpec)
  (h_agent_action : action.agent = j)
  (h_agent_spec : spec.direction.agent = j)
  (h_prob_mem : ∀ pair ∈ spec.prob_support,
      pair.1 ∈ p.agent_states ∧ pair.2 ∈ p.env_states)
  (h_prob_pos : ∀ pair ∈ spec.prob_support, 0 < p.prob pair.1 pair.2)
  (h_support_mem : ∀ b ∈ spec.support, b ∈ x.support)
  (h_der : directional_derivative_value i j spec p x κ h_κ h_agent_spec h_prob_mem h_prob_pos h_support_mem < 0)
  (h_positive_harm : 0 < harm j i action baseline h_agent_action) :
  ¬consent i j spec p x κ h_κ h_agent_spec h_prob_mem h_prob_pos h_support_mem :=
  no_consent_of_negative_derivative i j spec p x κ h_κ h_agent_spec h_prob_mem h_prob_pos h_support_mem h_der

/-- For specs built from actions, information contribution is zero (empty prob support). -/
lemma infoContribution_zero_of_actionSpec
  (p : Consent.ValueTypes.AgentEnvDistribution)
  (action : ActionSpec) (hσ : action.sigmaBalanced) :
  Consent.infoContribution (ActionSpec.directionSpecOfAction action hσ) p
    (by intro pair hp; cases hp)
    (by intro pair hp; cases hp) = 0 := by
  classical
  unfold Consent.infoContribution
  simp [ActionSpec.directionSpecOfAction_prob_support]

/-- Directional derivative equals minus the (restricted) mech sum for action-based specs. -/
lemma derivative_eq_neg_mechOn_of_actionSpec
  (i j : AgentId) (p : Consent.ValueTypes.AgentEnvDistribution)
  (baseline : LedgerState) (κ : ℝ) (hκ : 0 < κ)
  (action : ActionSpec) (hσ : action.sigmaBalanced)
  (h_agent : (ActionSpec.directionSpecOfAction action hσ).direction.agent = j) :
  Consent.directional_derivative_value i j (ActionSpec.directionSpecOfAction action hσ)
      p (bondConfigOf baseline) κ hκ h_agent
      (by intro pair hp; cases hp)
      (by intro pair hp; cases hp)
      (by intro b hb; exact hb) =
    - mechContributionOn (bondConfigOf baseline) (ActionSpec.directionSpecOfAction action hσ).support
        (ActionSpec.directionSpecOfAction action hσ) := by
  classical
  unfold Consent.directional_derivative_value
  simp [infoContribution_zero_of_actionSpec, mechContributionOn, Consent.mechContribution]

/-- Restricted derivative over `bondsOfAgent baseline j` equals minus the linearized sum. -/
lemma derivative_eq_neg_linSum_on_agent_bonds
  (i j : AgentId) (p : Consent.ValueTypes.AgentEnvDistribution)
  (baseline : LedgerState) (κ : ℝ) (hκ : 0 < κ)
  (action : ActionSpec) (hσ : action.sigmaBalanced)
  (h_agent : (ActionSpec.directionSpecOfAction action hσ).direction.agent = j) :
  Consent.directional_derivative_value i j (ActionSpec.directionSpecOfAction action hσ)
      p (bondConfigOf baseline) κ hκ h_agent
      (by intro pair hp; cases hp)
      (by intro pair hp; cases hp)
      (by intro b hb; exact hb) =
    - (bondsOfAgent baseline j).sum
        (fun b => linBondDelta (baseline.bond_multipliers b) (action.logStrain b)) := by
  classical
  have hsub : (ActionSpec.directionSpecOfAction action hσ).support ⊆ bondsOfAgent baseline j ∪ (ActionSpec.directionSpecOfAction action hσ).support := by
    intro b hb; exact Finset.mem_union_right.mpr (Or.inr hb)
  -- Use subset lemma specialized to equality on support, then rewrite with bondsOfAgent via filtering zeros.
  have := derivative_eq_neg_mechOn_of_actionSpec i j p baseline κ hκ action hσ h_agent
  have hmeq := mechContributionOn_eq_linSum_ofAction baseline j action hσ
  -- Re-express mech on support as mech on bonds using zeros outside support.
  have hrestrict :
      mechContributionOn (bondConfigOf baseline) (ActionSpec.directionSpecOfAction action hσ).support
        (ActionSpec.directionSpecOfAction action hσ)
      = mechContributionOn (bondConfigOf baseline) (bondsOfAgent baseline j)
        (ActionSpec.directionSpecOfAction action hσ) := by
    -- both sides equal the linearized sum because outside support the direction is zero
    have hx := mechContributionOn_eq_linSum_ofAction baseline j action hσ
    unfold mechContributionOn linBondDelta at hx
    -- rewrite RHS to linearized sum; LHS to the same linearized sum as well
    have hx' :
        mechContributionOn (bondConfigOf baseline) (ActionSpec.directionSpecOfAction action hσ).support
          (ActionSpec.directionSpecOfAction action hσ)
        = (ActionSpec.directionSpecOfAction action hσ).support.sum
            (fun b => ((baseline.bond_multipliers b - (baseline.bond_multipliers b)⁻¹) / 2)
                        * action.logStrain b) := by
      rfl
    simp [hx', hx]
  simpa [hrestrict, hmeq]

/-- Parametric consent corollary using any nonnegative upper bound on the remainder sum. -/
lemma consent_of_remainder_upper_bound
  (i j : AgentId) (p : Consent.ValueTypes.AgentEnvDistribution)
  (baseline : LedgerState) (κ : ℝ) (hκ : 0 < κ)
  (action : ActionSpec) (hσ : action.sigmaBalanced)
  (h_agent : (ActionSpec.directionSpecOfAction action hσ).direction.agent = j)
  (h_admissible : Foundation.admissible baseline)
  (remUpper : ℝ)
  (h_rem_upper :
    (bondsOfAgent baseline j).sum
      (fun b => remBondDelta (baseline.bond_multipliers b) (action.logStrain b))
    ≤ remUpper)
  (h_lin_nonneg :
    0 ≤ (bondsOfAgent baseline j).sum
      (fun b => linBondDelta (baseline.bond_multipliers b) (action.logStrain b)) + remUpper) :
  Consent.consent i j (ActionSpec.directionSpecOfAction action hσ)
      p (bondConfigOf baseline) κ hκ h_agent
      (by intro pair hp; cases hp)
      (by intro pair hp; cases hp)
      (by intro b hb; exact hb) := by
  classical
  have hdec := harm_decompose_linear_plus_rem i j action baseline rfl h_admissible
  have hlin := derivative_eq_neg_linSum_on_agent_bonds i j p baseline κ hκ action hσ h_agent
  -- Consent is sign of derivative ≥ 0; derivative = - linear sum; harm = linear + rem; use bound.
  unfold Consent.consent
  have hsum_le :
      (bondsOfAgent baseline j).sum (fun b => remBondDelta (baseline.bond_multipliers b) (action.logStrain b))
      ≤ remUpper := h_rem_upper
  have hineq :
      0 ≤ (bondsOfAgent baseline j).sum
          (fun b => linBondDelta (baseline.bond_multipliers b) (action.logStrain b)) + remUpper := h_lin_nonneg
  -- Convert to derivative sign using hlin
  have :
      0 ≤ - (Consent.directional_derivative_value i j (ActionSpec.directionSpecOfAction action hσ)
        p (bondConfigOf baseline) κ hκ h_agent
        (by intro pair hp; cases hp)
        (by intro pair hp; cases hp)
        (by intro b hb; exact hb)) := by
    -- derivative equals negative linear sum; apply bound
    simpa [hlin] using hineq
  simpa using (neg_nonneg.mp this)

/-! ## Harm matrix and minimax principle -/

structure HarmWitness where
  harm : ℝ
  variance : ℝ

noncomputable def harm_witness
    (i j : AgentId) (action : ActionSpec) (baseline : LedgerState)
    (h_agent : action.agent = i) : HarmWitness :=
{ harm := harm i j action baseline h_agent
  , variance := harm_variance action baseline j }

structure HarmMatrix where
  harm_values : AgentId → AgentId → ℝ
  nonneg : ∀ i j, i ≠ j → 0 ≤ harm_values i j
  self_zero : ∀ i, harm_values i i = 0

noncomputable def compute_harm_matrix_of
  (agents : List AgentId) (action : ActionSpec)
  (baseline : LedgerState) (h_admissible : Foundation.admissible baseline) : HarmMatrix :=
{ harm_values := fun i j =>
    if h : action.agent = i then harm i j action baseline h else 0
  , nonneg := by
      intro i j hneq
      by_cases h : action.agent = i
      · simpa [h] using harm_nonneg i j action baseline h h_admissible
      · simp [h]
  , self_zero := by
      intro i
      by_cases h : action.agent = i
      · simpa [h, harm_def, required_action_neutral_zero _ baseline h_admissible]
      · simp [h] }

noncomputable def compute_harm_matrix
  (agents : List AgentId) (action : ActionSpec) (baseline : LedgerState) : HarmMatrix :=
if h : Foundation.admissible baseline then
  compute_harm_matrix_of agents action baseline h
else
{ harm_values := fun _ _ => 0
  , nonneg := by intro i j _; simp
  , self_zero := by intro i; simp }

noncomputable def max_harm (matrix : HarmMatrix) (agents : List AgentId) : ℝ :=
  agents.foldl (fun acc i =>
    agents.foldl (fun inner j => max inner (matrix.harm_values i j)) acc) 0

lemma minimax_harm_principle
  (actions : List ActionSpec) (baseline : LedgerState) (agents : List AgentId)
  (h_nonempty : actions ≠ []) (h_admissible : Foundation.admissible baseline) :
  ∃ optimal ∈ actions, ∀ a ∈ actions,
      max_harm (compute_harm_matrix_of agents optimal baseline h_admissible) agents ≤
      max_harm (compute_harm_matrix_of agents a baseline h_admissible) agents := by
  classical
  have hlen : 0 < actions.length := List.length_pos_of_ne_nil h_nonempty
  let scores : List ℝ := actions.map fun act =>
    max_harm (compute_harm_matrix_of agents act baseline h_admissible) agents
  obtain ⟨best, hbest, hbest_min⟩ :=
    List.exists_minimal_of_nonempty scores (by simpa [scores] using hlen)
  rcases List.mem_map.mp hbest with ⟨opt, hopt_mem, rfl⟩
  refine ⟨opt, hopt_mem, ?_⟩
  intro a ha
  have := hbest_min (by exact List.mem_map.mpr ⟨a, ha, rfl⟩)
  simpa [scores]

/-! ## Virtue-aligned corollaries -/

lemma love_equalizes_harm
  (i j : AgentId) (actionᵢ actionⱼ : ActionSpec) (baseline : LedgerState)
  (h_agentᵢ : actionᵢ.agent = i) (h_agentⱼ : actionⱼ.agent = j)
  (h_match : actionᵢ.factor = actionⱼ.factor)
  (h_admissible : Foundation.admissible baseline) :
  harm i j actionᵢ baseline h_agentᵢ = harm j i actionⱼ baseline h_agentⱼ := by
  classical
  unfold harm required_action agentCost
  have : applyAction actionᵢ baseline = applyAction actionⱼ baseline := by
    ext b
    have := congrArg (fun f => f b) h_match
    simp [applyAction, this]
  simp [this]

lemma forgiveness_transfers_harm
  (creditor debtor : AgentId) (action : ActionSpec) (baseline : LedgerState)
  (h_agent : action.agent = creditor)
  (h_disjoint : Disjoint action.support (bondsOfAgent baseline debtor))
  (h_admissible : Foundation.admissible baseline) :
  harm creditor debtor action baseline h_agent = 0 :=
  harm_zero_of_support_disjoint _ _ action baseline h_agent h_disjoint h_admissible

lemma sacrifice_absorbs_harm
  (sacrificer beneficiary : AgentId) (action : ActionSpec)
  (baseline : LedgerState) (h_agent : action.agent = sacrificer)
  (h_disjoint : Disjoint action.support (bondsOfAgent baseline beneficiary))
  (h_admissible : Foundation.admissible baseline) :
  harm sacrificer beneficiary action baseline h_agent = 0 :=
  harm_zero_of_support_disjoint _ _ action baseline h_agent h_disjoint h_admissible

end Harm
end Ethics
end IndisputableMonolith
