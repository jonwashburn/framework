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

noncomputable def value_of_agent
    (i : AgentId)
    (p : AgentEnvDistribution)
    (x : BondConfig)
    (κ : ℝ)
    (h_κ : 0 < κ) : ℝ :=
  value p x κ h_κ / 2

noncomputable def welfare_transform (v : ℝ) : ℝ := v

noncomputable def total_welfare
    (agents : List AgentId)
    (values : AgentId → ℝ) : ℝ :=
  agents.foldl (fun acc i => acc + welfare_transform (values i)) 0

end ValueFunctional
end Ethics
end IndisputableMonolith
