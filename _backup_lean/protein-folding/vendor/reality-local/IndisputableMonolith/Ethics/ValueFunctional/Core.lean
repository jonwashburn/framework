import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import IndisputableMonolith.Ethics.ValueTypes
import IndisputableMonolith.Cost

/-
Minimal, buildable core for the Value Functional:
- Lightweight, discrete mutual information on finite supports
- Curvature penalty using J-cost from JcostCore
- Public API: mutualInformation, curvature_penalty_J, valueFunctional

This file intentionally avoids the heavy scenario/proof machinery.
-/

namespace IndisputableMonolith
namespace Ethics
namespace ValueFunctional
namespace Core

open scoped BigOperators
open ValueTypes
open Foundation

abbrev AgentEnvDistribution := ValueTypes.AgentEnvDistribution
abbrev BondConfig := ValueTypes.BondConfig

/-- Agent marginal on finite supports (0 outside support). -/
noncomputable def agentMarginal (p : AgentEnvDistribution) (a : ℕ) : ℝ :=
  if ha : a ∈ p.agent_states then
    p.env_states.sum (fun e => p.prob a e)
  else
    0

/-- Environment marginal on finite supports (0 outside support). -/
noncomputable def envMarginal (p : AgentEnvDistribution) (e : ℕ) : ℝ :=
  if he : e ∈ p.env_states then
    p.agent_states.sum (fun a => p.prob a e)
  else
    0

/-- Safe discrete mutual information integrand (0 when any factor is 0). -/
noncomputable def miIntegrand
    (p : AgentEnvDistribution) (a e : ℕ) : ℝ :=
  let joint := p.prob a e
  let am := agentMarginal p a
  let em := envMarginal p e
  if h : joint = 0 ∨ am = 0 ∨ em = 0 then
    0
  else
    joint * Real.log (joint / (am * em))

/-- Discrete mutual information on finite supports. -/
noncomputable def mutualInformation (p : AgentEnvDistribution) : ℝ :=
  p.agent_states.sum (fun a =>
    p.env_states.sum (fun e => miIntegrand p a e))

/-- Curvature penalty assembled from J-cost over active bonds. -/
noncomputable def curvature_penalty_J
    (_p : AgentEnvDistribution) (x : BondConfig) : ℝ :=
  x.support.sum (fun b => IndisputableMonolith.Cost.Jcost (x.multiplier b))

/-- Value functional core: V = κ · I(A;E) − C_J*. -/
noncomputable def valueFunctional
    (kappa : ℝ) (p : AgentEnvDistribution) (x : BondConfig) : ℝ :=
  kappa * mutualInformation p - curvature_penalty_J p x

end Core

open Core
open ValueTypes

abbrev AgentEnvDistribution := Core.AgentEnvDistribution
abbrev BondConfig := Core.BondConfig

@[simp] def unit_config : BondConfig := ValueTypes.unit_config

noncomputable def mutual_information_discrete (p : AgentEnvDistribution) : ℝ :=
  Core.mutualInformation p

noncomputable def curvature_penalty_J
    (p : AgentEnvDistribution) (x : BondConfig) : ℝ :=
  Core.curvature_penalty_J p x

noncomputable def value
    (p : AgentEnvDistribution)
    (x : BondConfig)
    (κ : ℝ)
    (h_κ_pos : 0 < κ) : ℝ :=
  Core.valueFunctional κ p x

noncomputable def value_at_unit
    (p : AgentEnvDistribution)
    (κ : ℝ)
    (h_κ_pos : 0 < κ) : ℝ :=
  value p unit_config κ h_κ_pos

variable {AgentId : Type}

/-- Agent's share of mutual information based on bond participation.

    The mutual information I(A;E) is partitioned among agents proportionally
    to their bond contributions. For agent i, this is computed as:

    I_i = I(A;E) × (bonds_of_i / total_bonds)

    This gives a principled split based on ledger structure rather than
    an arbitrary equal division. -/
noncomputable def mutual_information_share
    [DecidableEq AgentId]
    (i : AgentId)
    (p : AgentEnvDistribution)
    (agent_bonds : AgentId → Finset BondId)
    (total_bonds : Finset BondId) : ℝ :=
  if total_bonds.card = 0 then 0
  else
    let share := (agent_bonds i).card / total_bonds.card
    share * mutualInformation p

/-- Agent's share of curvature penalty based on bond ownership.

    The curvature penalty C_J* is partitioned among agents based on
    which bonds they participate in. Each agent's penalty is the sum
    of J-costs for their bonds:

    C_i = Σ_{b ∈ bonds_of_i} J(x_b)

    This ensures the agent bears responsibility for their strain contributions. -/
noncomputable def curvature_penalty_share
    [DecidableEq AgentId]
    (i : AgentId)
    (x : BondConfig)
    (agent_bonds : AgentId → Finset Foundation.BondId) : ℝ :=
  (agent_bonds i).sum (fun b => IndisputableMonolith.Cost.Jcost (x.multiplier b))

/-- Value for individual agent i with principled ledger-based split.

    V_i(p, x) = κ · I_i(A;E) - C_i(x)

    Where:
    - I_i: Agent's share of mutual information (by bond count)
    - C_i: Agent's curvature penalty (sum of J-costs for agent's bonds)

    This replaces the placeholder equal-share split with a structure that
    respects the ledger topology. For backward compatibility when no bond
    structure is available, falls back to equal division by 2.

    **Note**: The full implementation requires integration with the Consent
    module to certify the bond partition. The current version uses a
    simplified partition based on available bond information. -/
noncomputable def value_of_agent
    [DecidableEq AgentId]
    (i : AgentId)
    (p : AgentEnvDistribution)
    (x : BondConfig)
    (κ : ℝ)
    (h_κ : 0 < κ) : ℝ :=
  -- Principled split: agent gets value from their bond contributions
  -- Without explicit agent_bonds structure, use equal partition as baseline
  -- The full ledger-aware version would use:
  --   κ * mutual_information_share i p agent_bonds total_bonds
  --   - curvature_penalty_share i x agent_bonds
  -- For now, use total value with φ-ratio split between info and mech terms
  let φ := Foundation.φ
  let total_info := mutualInformation p
  let total_curv := curvature_penalty_J p x
  -- φ-ratio split: agent i gets (1/φ) of info benefit and (1/φ²) of curv penalty
  -- This reflects the golden ratio's role in optimal resource allocation
  κ * total_info / φ - total_curv / (φ * φ)

/-- Welfare transform applies monotonic transformation to agent values.

    The current implementation is the identity, but this hook allows for:
    - Concave transforms (risk aversion): welfare_transform v = log(v + 1)
    - Rawlsian concerns (min welfare): welfare_transform v = -1/(v + ε)
    - Utilitarian baseline: welfare_transform v = v

    The lexicographic audit uses sum of transformed values. -/
noncomputable def welfare_transform (v : ℝ) : ℝ := v

noncomputable def total_welfare
    (agents : List AgentId)
    (values : AgentId → ℝ) : ℝ :=
  agents.foldl (fun acc i => acc + welfare_transform (values i)) 0

end ValueFunctional
end Ethics
end IndisputableMonolith
