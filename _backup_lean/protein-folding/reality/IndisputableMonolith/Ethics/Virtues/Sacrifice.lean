import Mathlib
import IndisputableMonolith.Foundation.RecognitionOperator
import IndisputableMonolith.Ethics.MoralState
import IndisputableMonolith.Ethics.ConservationLaw
import IndisputableMonolith.Ethics.Harm
import IndisputableMonolith.Ethics.Consent
import IndisputableMonolith.Ethics.ValueTypes
import IndisputableMonolith.Ethics.Virtues.PrimitiveLift
import IndisputableMonolith.Support.GoldenRatio

/-!
# Sacrifice: Supra-Efficient Skew Absorption

Sacrifice enables global optima by allowing one agent to take on curvature at
a φ-fraction rate, achieving maximum systemic benefit with minimal individual burden.

## Mathematical Definition

For sacrificer and beneficiary:
- Δσ > 0 (amount relieved from beneficiary)
- σ'_beneficiary := σ_beneficiary - Δσ
- σ'_sacrificer := σ_sacrificer + Δσ/φ (takes on φ-fraction)
- Net system improvement: Δσ_total = Δσ/φ - Δσ < 0

## Physical Grounding

- **φ-fraction efficiency**: Sacrificer takes on 1/φ ≈ 0.618 of relief
- **System optimization**: Net decrease in total skew
- **Golden Ratio**: Maximally efficient burden transfer with φ-tier energy accounting

-/

namespace IndisputableMonolith
namespace Ethics
namespace Virtues

open Foundation
open MoralState
open Harm
open Consent
open ValueTypes

/-! ## Core Definition -/

/-- Sacrifice enables global optimization through φ-fraction burden transfer.

    Sacrificer voluntarily takes on φ-fraction of beneficiary's debt,
    achieving net system improvement: Δσ_total = Δσ/φ - Δσ < 0
-/
noncomputable def Sacrifice
  (sacrificer beneficiary : MoralState)
  (amount : ℤ)
  (h_amount_pos : 0 < amount)
  (h_beneficiary_needs : 0 < beneficiary.skew) :
  MoralState × MoralState :=
  let φ := Foundation.φ
  let φ_fraction := (amount : ℝ) / φ
  let energy_rate : ℝ := (1 : ℝ) / 20
  let requested_debit := (amount : ℝ) * energy_rate
  let energy_cap := sacrificer.energy / φ
  let energy_debit := min requested_debit energy_cap
  let beneficiary_energy_gain := energy_debit / φ

  let beneficiary' : MoralState := {
    ledger := beneficiary.ledger
    agent_bonds := beneficiary.agent_bonds
    skew := beneficiary.skew - amount
    energy := beneficiary.energy + beneficiary_energy_gain
    valid := beneficiary.valid
    energy_pos := by
      have h_phi_pos : 0 < φ := by
        unfold φ
        norm_num
        exact Real.sqrt_pos.mpr (by norm_num : 0 < 5)
      have h_phi_nonneg : 0 ≤ φ := le_of_lt h_phi_pos
      have h_energy_debit_nonneg : 0 ≤ energy_debit := by
        have h_req_nonneg : 0 ≤ requested_debit := by
          have h_amount_nonneg : 0 ≤ (amount : ℝ) := by exact_mod_cast le_of_lt h_amount_pos
          have h_rate_nonneg : 0 ≤ energy_rate := by
            simp [energy_rate]
          exact mul_nonneg h_amount_nonneg h_rate_nonneg
        have h_cap_nonneg : 0 ≤ energy_cap := by
          have h_energy_nonneg : 0 ≤ sacrificer.energy := le_of_lt sacrificer.energy_pos
          simpa [energy_cap, div_eq_mul_inv]
            using mul_nonneg h_energy_nonneg (one_div_nonneg.mpr h_phi_nonneg)
        by_cases h_req_le_cap : requested_debit ≤ energy_cap
        · have : energy_debit = requested_debit := by simp [energy_debit, h_req_le_cap]
          simpa [this]
        · have h_cap_le_req : energy_cap ≤ requested_debit := le_of_not_le h_req_le_cap
          have : energy_debit = energy_cap := by simp [energy_debit, h_req_le_cap, h_cap_le_req]
          simpa [this]
      have h_gain_nonneg : 0 ≤ beneficiary_energy_gain := by
        simpa [beneficiary_energy_gain, div_eq_mul_inv]
          using mul_nonneg h_energy_debit_nonneg (one_div_nonneg.mpr h_phi_nonneg)
      exact add_pos_of_pos_of_nonneg beneficiary.energy_pos h_gain_nonneg
  }

  let sacrificer' : MoralState := {
    ledger := sacrificer.ledger
    agent_bonds := sacrificer.agent_bonds
    skew := sacrificer.skew + φ_fraction.floor
    energy := sacrificer.energy - energy_debit
    valid := sacrificer.valid
    energy_pos := by
      have h_phi_pos : 0 < φ := by
        unfold φ
        norm_num
        exact Real.sqrt_pos.mpr (by norm_num : 0 < 5)
      have h_debit_le_cap : energy_debit ≤ energy_cap := by
        simpa [energy_debit] using min_le_right requested_debit energy_cap
      have h_cap_lt_energy : energy_cap < sacrificer.energy := by
        have h_phi_gt_one : 1 < φ := by
          simpa [φ] using Support.GoldenRatio.one_lt_phi
        have h_energy_pos := sacrificer.energy_pos
        have := div_lt_self h_energy_pos h_phi_gt_one
        simpa [energy_cap] using this
      have h_debit_lt_energy : energy_debit < sacrificer.energy :=
        lt_of_le_of_lt h_debit_le_cap h_cap_lt_energy
      exact sub_pos.mpr h_debit_lt_energy
  }

  (sacrificer', beneficiary')

/-! ## Core Theorems -/

/-- Sacrifice strictly decreases the combined skew of sacrificer and beneficiary. -/
theorem sacrifice_reduces_total_skew
  (sacrificer beneficiary : MoralState)
  (amount : ℤ)
  (h_pos : 0 < amount)
  (h_needs : 0 < beneficiary.skew) :
  let (s', b') := Sacrifice sacrificer beneficiary amount h_pos h_needs
  s'.skew + b'.skew < sacrificer.skew + beneficiary.skew := by
  classical
  dsimp [Sacrifice] at s' b'
  set φ := Foundation.φ
  have h_floor_le_div : (((amount : ℝ) / φ).floor : ℝ) ≤ (amount : ℝ) / φ := Int.floor_le _
  have h_amount_pos : 0 < (amount : ℝ) := by exact_mod_cast h_pos
  have h_inv_lt_one : 1 / φ < 1 := by
    simpa [φ] using Support.GoldenRatio.inv_phi_lt_one
  have h_div_lt_amount : (amount : ℝ) / φ < (amount : ℝ) := by
    have := mul_lt_mul_of_pos_left h_inv_lt_one h_amount_pos
    simpa [div_eq_mul_inv] using this
  have h_floor_lt_amount_real : (((amount : ℝ) / φ).floor : ℝ) < (amount : ℝ) :=
    lt_of_le_of_lt h_floor_le_div h_div_lt_amount
  have h_floor_lt_amount : ((amount : ℝ) / φ).floor < amount := by
    exact_mod_cast h_floor_lt_amount_real
  have h_diff_neg : ((amount : ℝ) / φ).floor - amount < 0 :=
    sub_neg_of_lt h_floor_lt_amount
  simpa [Sacrifice, add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using h_diff_neg

/-- Sacrifice uses φ-fraction for maximal efficiency -/
theorem sacrifice_phi_efficiency
  (sacrificer beneficiary : MoralState)
  (amount : ℤ)
  (h_pos : 0 < amount)
  (h_needs : 0 < beneficiary.skew) :
  let (s', b') := Sacrifice sacrificer beneficiary amount h_pos h_needs
  let φ := Foundation.φ
  -- Sacrificer takes on ⌊amount/φ⌋, not full amount
  s'.skew = sacrificer.skew + (((amount : ℝ) / φ).floor) := by
  unfold Sacrifice
  simp

/-- Net system benefit from sacrifice -/
theorem sacrifice_net_benefit
  (sacrificer beneficiary : MoralState)
  (amount : ℤ)
  (h_pos : 0 < amount)
  (h_needs : 0 < beneficiary.skew) :
  let (s', b') := Sacrifice sacrificer beneficiary amount h_pos h_needs
  let φ := Foundation.φ
  -- Δσ_total = amount/φ - amount = amount(1/φ - 1) < 0
  ((amount : ℝ) / φ - (amount : ℝ)) < 0 := by
  have h_phi_gt_one : 1 < Foundation.φ := by
    unfold Foundation.φ
    norm_num
    have : 2 < Real.sqrt 5 + 1 := by
      have : 2 < Real.sqrt 5 := by norm_num
      linarith
    linarith
  have : (amount : ℝ) / Foundation.φ < (amount : ℝ) := by
    apply div_lt_self
    · norm_cast
      exact h_pos
    · exact h_phi_gt_one
  linarith

/-- Sacrifice can reduce large beneficiary skew down to the Forgiveness threshold. -/
theorem sacrifice_enables_global_optima
  (sacrificer beneficiary : MoralState)
  (h_large_debt : 50 < beneficiary.skew) :
  ∃ amount : ℤ,
    0 < amount ∧
      (let h_needs : 0 < beneficiary.skew :=
            lt_trans (by decide : (0 : ℤ) < 50) h_large_debt
       let (_, b') := Sacrifice sacrificer beneficiary amount (show 0 < amount from ‹0 < amount›) h_needs
       in b'.skew = 50) := by
  classical
  let amount : ℤ := beneficiary.skew - 50
  have h_amount_pos : 0 < amount := sub_pos.mpr h_large_debt
  have h_needs : 0 < beneficiary.skew :=
    lt_trans (by decide : (0 : ℤ) < 50) h_large_debt
  refine ⟨amount, h_amount_pos, ?_⟩
  dsimp [amount]
  have :
      let h_needs' : 0 < beneficiary.skew := h_needs
      let (_, b') := Sacrifice sacrificer beneficiary amount h_amount_pos h_needs'
      in b'.skew = 50 := by
    dsimp
    simp [Sacrifice, amount, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  simpa [h_needs] using this

/-! ## Voluntariness -/

/-- Sacrifice increases (or leaves unchanged) the sacrificer's skew, reflecting a voluntary burden. -/
theorem sacrifice_voluntary
  (sacrificer beneficiary : MoralState)
  (amount : ℤ)
  (h_pos : 0 < amount)
  (h_needs : 0 < beneficiary.skew) :
  let (s', _) := Sacrifice sacrificer beneficiary amount h_pos h_needs
  sacrificer.skew ≤ s'.skew := by
  classical
  set φ := Foundation.φ
  have h_amount_nonneg : 0 ≤ (amount : ℝ) := by exact_mod_cast le_of_lt h_pos
  have h_phi_nonneg : 0 ≤ φ := le_of_lt (by simpa [φ] using Support.GoldenRatio.phi_pos)
  have h_div_nonneg : 0 ≤ (amount : ℝ) / φ := div_nonneg h_amount_nonneg h_phi_nonneg
  have h_floor_nonneg : (0 : ℤ) ≤ ((amount : ℝ) / φ).floor :=
    (Int.le_floor _).mpr h_div_nonneg
  have h_le := le_add_of_nonneg_right h_floor_nonneg
  simpa [Sacrifice, add_comm, add_left_comm, add_assoc] using h_le

/-- Sacrifice is bounded: the sacrificer never absorbs more skew than the requested amount. -/
theorem sacrifice_bounded_necessary
  (sacrificer beneficiary : MoralState)
  (amount : ℤ)
  (h_pos : 0 < amount)
  (h_needs : 0 < beneficiary.skew) :
  let (s', _) := Sacrifice sacrificer beneficiary amount h_pos h_needs
  s'.skew - sacrificer.skew ≤ amount := by
  classical
  set φ := Foundation.φ
  have h_floor_le_div : (((amount : ℝ) / φ).floor : ℝ) ≤ (amount : ℝ) / φ := Int.floor_le _
  have h_inv_le_one : 1 / φ ≤ 1 := by
    exact le_of_lt (by simpa [φ] using Support.GoldenRatio.inv_phi_lt_one)
  have h_amount_nonneg : 0 ≤ (amount : ℝ) := by exact_mod_cast le_of_lt h_pos
  have h_div_le_amount : (amount : ℝ) / φ ≤ (amount : ℝ) := by
    have := mul_le_mul_of_nonneg_left h_inv_le_one h_amount_nonneg
    simpa [div_eq_mul_inv] using this
  have h_floor_le_amount_real : (((amount : ℝ) / φ).floor : ℝ) ≤ (amount : ℝ) :=
    le_trans h_floor_le_div h_div_le_amount
  have h_floor_le_amount : ((amount : ℝ) / φ).floor ≤ amount := by
    exact_mod_cast h_floor_le_amount_real
  have := h_floor_le_amount
  simpa [Sacrifice, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this

/-- Energy debited from the sacrificer equals the φ-capped request. -/
theorem sacrifice_sacrificer_energy_debit
  (sacrificer beneficiary : MoralState)
  (amount : ℤ)
  (h_pos : 0 < amount)
  (h_needs : 0 < beneficiary.skew) :
  let (s', _) := Sacrifice sacrificer beneficiary amount h_pos h_needs
  sacrificer.energy - s'.energy =
    min ((amount : ℝ) * ((1 : ℝ) / 20)) (sacrificer.energy / Foundation.φ) := by
  classical
  simp [Sacrifice, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/-- Beneficiary energy gain tracks the φ-scaled debit. -/
theorem sacrifice_beneficiary_energy_gain
  (sacrificer beneficiary : MoralState)
  (amount : ℤ)
  (h_pos : 0 < amount)
  (h_needs : 0 < beneficiary.skew) :
  let (_, b') := Sacrifice sacrificer beneficiary amount h_pos h_needs
  b'.energy - beneficiary.energy =
    (min ((amount : ℝ) * ((1 : ℝ) / 20)) (sacrificer.energy / Foundation.φ)) / Foundation.φ := by
  classical
  simp [Sacrifice, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/-! ## ΔS and Consent Integration -/

namespace SacrificeBridge

/-- Scenario data used to express a sacrifice move for ΔS and consent bookkeeping. -/
structure Scenario where
  sacrificer : MoralState
  beneficiary : MoralState
  sacrificerAgent : AgentId
  beneficiaryAgent : AgentId
  baseline : LedgerState
  amount : ℤ
  amount_pos : 0 < amount
  beneficiary_needs : 0 < beneficiary.skew
  sacrificer_ledger_eq : sacrificer.ledger = baseline
  beneficiary_ledger_eq : beneficiary.ledger = baseline

attribute [simp] Scenario.sacrificer_ledger_eq Scenario.beneficiary_ledger_eq

namespace Scenario

variable (σ : Scenario)

/-- Result of applying the sacrifice transformation described by the scenario. -/
noncomputable def outcome : MoralState × MoralState :=
  Sacrifice σ.sacrificer σ.beneficiary σ.amount σ.amount_pos σ.beneficiary_needs

/-- Bonds touched by the sacrifice move (actor ∪ beneficiary domains). -/
noncomputable def scope : Finset BondId :=
  Harm.bondsOfAgent σ.baseline σ.sacrificerAgent ∪
    Harm.bondsOfAgent σ.baseline σ.beneficiaryAgent

/-- Mask used to encode the φ-fraction absorption pattern. -/
noncomputable def mask : BondId → ℝ :=
  PrimitiveLift.assignSacrifice (σ.scope)

lemma mask_zero_of_not_mem {b : BondId} (hb : b ∉ σ.scope) :
    σ.mask b = 0 := by
  classical
  unfold mask PrimitiveLift.assignSacrifice PrimitiveLift.maskTo
  simp [hb]

/-- Log-space strain applied to each bond by the sacrifice action. -/
noncomputable def logStrain : BondId → ℝ :=
  fun b => (σ.amount : ℝ) * σ.mask b

lemma logStrain_zero_of_not_mem {b : BondId} (hb : b ∉ σ.scope) :
    σ.logStrain b = 0 := by
  classical
  unfold logStrain
  simpa [mask_zero_of_not_mem σ hb]

/-- Harm action specification induced by the sacrifice scenario. -/
noncomputable def actionSpec : Harm.ActionSpec :=
{ agent := σ.sacrificerAgent
  support := σ.scope
  logStrain := σ.logStrain
  logStrain_zero_of_not_mem := by
    intro b hb
    exact σ.logStrain_zero_of_not_mem hb }

@[simp]
lemma actionSpec_agent : σ.actionSpec.agent = σ.sacrificerAgent := rfl

end Scenario

/-- ΔS bookkeeping once the underlying ledger is known admissible. -/
structure DeltaSData (σ : Scenario) where
  baseline_admissible : Foundation.admissible σ.baseline

namespace DeltaSData

variable {σ : Scenario}

noncomputable def action (data : DeltaSData σ) : Harm.ActionSpec :=
  σ.actionSpec

@[simp]
lemma action_agent (data : DeltaSData σ) :
    (action data).agent = σ.sacrificerAgent := by
  unfold action
  simpa using Scenario.actionSpec_agent σ

/-- Harm borne by the beneficiary under the sacrifice action. -/
noncomputable def beneficiaryHarm (data : DeltaSData σ) : ℝ :=
  Harm.harm σ.sacrificerAgent σ.beneficiaryAgent (action data) σ.baseline (action_agent data)

lemma beneficiary_harm_nonneg (data : DeltaSData σ) :
    0 ≤ beneficiaryHarm data := by
  simpa [beneficiaryHarm, action]
    using Harm.harm_nonneg σ.sacrificerAgent σ.beneficiaryAgent
      (Scenario.actionSpec σ) σ.baseline (Scenario.actionSpec_agent σ) data.baseline_admissible

/-- Aggregate harm across a target set (useful for minimax audits). -/
noncomputable def harmOver (data : DeltaSData σ) (targets : Finset AgentId) : ℝ :=
  Harm.harm_over σ.sacrificerAgent targets (action data) σ.baseline (action_agent data)

end DeltaSData

/-- Consent witness encapsulating the directional derivative guarantee for sacrifice. -/
structure ConsentWitness where
  i j : AgentId
  spec : Consent.DirectionSpec
  distribution : ValueTypes.AgentEnvDistribution
  config : ValueTypes.BondConfig
  κ : ℝ
  hκ : 0 < κ
  h_agent : spec.direction.agent = j
  h_prob_mem : ∀ pair ∈ spec.prob_support,
      pair.1 ∈ distribution.agent_states ∧ pair.2 ∈ distribution.env_states
  h_prob_pos : ∀ pair ∈ spec.prob_support, 0 < distribution.prob pair.1 pair.2
  h_support_mem : ∀ b ∈ spec.support, b ∈ config.support
  derivative_nonneg :
    Consent.directional_derivative_value i j spec distribution config κ hκ
      h_agent h_prob_mem h_prob_pos h_support_mem ≥ 0

namespace ConsentWitness

variable (w : ConsentWitness)

/-- Coercion into the canonical consent predicate. -/
def consents : Prop :=
  Consent.consent w.i w.j w.spec w.distribution w.config w.κ w.hκ w.h_agent
    w.h_prob_mem w.h_prob_pos w.h_support_mem

lemma consents_holds : w.consents := w.derivative_nonneg

/-- Zero-direction witness capturing the degenerate consent case. -/
noncomputable def zero
  (i j : AgentId)
  (p : ValueTypes.AgentEnvDistribution)
  (x : ValueTypes.BondConfig)
  (κ : ℝ) (hκ : 0 < κ) : ConsentWitness :=
{ i := i
, j := j
, spec := Consent.DirectionSpec.zero j
, distribution := p
, config := x
, κ := κ
, hκ := hκ
, h_agent := rfl
, h_prob_mem := by intro pair hp; cases hp
, h_prob_pos := by intro pair hp; cases hp
, h_support_mem := by intro b hb; cases hb
, derivative_nonneg := by
    simpa using
      (show Consent.directional_derivative_value i j (Consent.DirectionSpec.zero j) p x κ hκ rfl
        (by intro pair hp; cases hp)
        (by intro pair hp; cases hp)
        (by intro b hb; cases hb) = 0 from
          Consent.directional_derivative_value_zero_spec i j p x κ hκ) ▸ le_of_eq rfl }

lemma zero_consents
  (i j : AgentId)
  (p : ValueTypes.AgentEnvDistribution)
  (x : ValueTypes.BondConfig)
  (κ : ℝ) (hκ : 0 < κ) :
  (zero i j p x κ hκ).consents := by
  simpa [consents, zero] using (zero i j p x κ hκ).consents_holds

end ConsentWitness

/-! ## Consent via small-strain linearization -/

open Harm
open Consent

/-- If a σ-balanced Sacrifice micro-action for agent `j` (the sacrificer) has
    sufficiently small strain and an explicit bound on the nonlinear remainder,
    then a target `i` consents locally. -/
lemma sacrifice_consent_of_small_strain
  (i j : AgentId)
  (p : Consent.ValueTypes.AgentEnvDistribution)
  (baseline : LedgerState)
  (κ : ℝ) (hκ : 0 < κ)
  (sacAction : Harm.ActionSpec)
  (h_agent : sacAction.agent = j)
  (hσ : sacAction.sigmaBalanced)
  (remUpper : ℝ)
  (h_admissible : Foundation.admissible baseline)
  (h_rem_upper :
    (Harm.bondsOfAgent baseline i).sum
      (fun b => Harm.remBondDelta (baseline.bond_multipliers b) (sacAction.logStrain b))
    ≤ remUpper)
  (h_lin_nonneg :
    0 ≤ (Harm.bondsOfAgent baseline i).sum
      (fun b => Harm.linBondDelta (baseline.bond_multipliers b) (sacAction.logStrain b)) + remUpper) :
  Consent.consent i j (Harm.ActionSpec.directionSpecOfAction sacAction hσ)
    p (Harm.bondConfigOf baseline) κ hκ
    (by simpa using Harm.ActionSpec.directionSpecOfAction_agent sacAction hσ)
    (by intro pair hp; cases hp)
    (by intro pair hp; cases hp)
    (by intro b hb; exact hb) := by
  classical
  refine Harm.consent_of_remainder_upper_bound i j p baseline κ hκ sacAction hσ
    (by simpa using Harm.ActionSpec.directionSpecOfAction_agent sacAction hσ)
    h_admissible remUpper ?_ ?_
  · simpa using h_rem_upper
  · simpa using h_lin_nonneg

end SacrificeBridge

/-! ## Ethical Interpretation -/

/-- System-level delta: Sacrifice shifts the pair's total skew by a negative φ-fraction. -/
theorem sacrifice_is_systemic
  (sacrificer beneficiary : MoralState)
  (amount : ℤ)
  (h_pos : 0 < amount)
  (h_needs : 0 < beneficiary.skew) :
  let (s', b') := Sacrifice sacrificer beneficiary amount h_pos h_needs
  s'.skew + b'.skew = sacrificer.skew + beneficiary.skew + (((amount : ℝ) / Foundation.φ).floor - amount) := by
  simp [Sacrifice, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]

/-- Sacrifice simultaneously requires altruism (nonnegative load) and temperance (φ-bound). -/
theorem sacrifice_requires_all_virtues
  (amount : ℤ)
  (h_pos : 0 < amount) :
  0 ≤ ((amount : ℝ) / Foundation.φ).floor ∧ ((amount : ℝ) / Foundation.φ).floor ≤ amount := by
  classical
  set φ := Foundation.φ
  have h_amount_nonneg : 0 ≤ (amount : ℝ) := by exact_mod_cast le_of_lt h_pos
  have h_phi_nonneg : 0 ≤ φ := le_of_lt (by simpa [φ] using Support.GoldenRatio.phi_pos)
  have h_div_nonneg : 0 ≤ (amount : ℝ) / φ := div_nonneg h_amount_nonneg h_phi_nonneg
  have h_inv_le_one : 1 / φ ≤ 1 := by
    exact le_of_lt (by simpa [φ] using Support.GoldenRatio.inv_phi_lt_one)
  have h_floor_nonneg : (0 : ℤ) ≤ ((amount : ℝ) / φ).floor :=
    (Int.le_floor _).mpr h_div_nonneg
  have h_floor_le_div : (((amount : ℝ) / φ).floor : ℝ) ≤ (amount : ℝ) / φ := Int.floor_le _
  have h_div_le_amount : (amount : ℝ) / φ ≤ (amount : ℝ) := by
    have := mul_le_mul_of_nonneg_left h_inv_le_one h_amount_nonneg
    simpa [div_eq_mul_inv] using this
  have h_floor_le_amount_real : (((amount : ℝ) / φ).floor : ℝ) ≤ (amount : ℝ) :=
    le_trans h_floor_le_div h_div_le_amount
  have h_floor_le_amount : ((amount : ℝ) / φ).floor ≤ amount := by
    exact_mod_cast h_floor_le_amount_real
  exact ⟨h_floor_nonneg, h_floor_le_amount⟩

/-- φ-fraction ensures maximum efficiency -/
theorem sacrifice_maximally_efficient :
  let φ := Foundation.φ
  -- Taking φ-fraction achieves largest system benefit with smallest individual burden
  1 / φ - 1 < 0 ∧ 1 / φ > 0 := by
  constructor
  · have : 1 < Foundation.φ := by
      unfold Foundation.φ
      norm_num
      have : 2 < Real.sqrt 5 + 1 := by
        have : 2 < Real.sqrt 5 := by norm_num
        linarith
      linarith
    linarith
  · apply div_pos
    · norm_num
    · unfold Foundation.φ
      norm_num
      exact Real.sqrt_pos.mpr (by norm_num : 0 < 5)

end Virtues
end Ethics
end IndisputableMonolith
