import Mathlib
import IndisputableMonolith.Foundation.RecognitionOperator
import IndisputableMonolith.Ethics.MoralState
import IndisputableMonolith.Ethics.ConservationLaw
import IndisputableMonolith.Ethics.Harm
import IndisputableMonolith.Ethics.Consent
import IndisputableMonolith.Ethics.ValueTypes
import IndisputableMonolith.Support.GoldenRatio
import IndisputableMonolith.Ethics.Virtues.Love
import IndisputableMonolith.Ethics.Virtues.PrimitiveLift

/-!
# Forgiveness: Controlled Skew Transfer with Energy Cost

Forgiveness enables cascade prevention by allowing a creditor to absorb a portion
of a debtor's skew, paying an energy cost to stabilize the system.

## Mathematical Definition

For creditor and debtor states:
1. **Skew transfer**: Move up to `amount` skew from debtor to creditor
2. **Energy penalty**: Creditor pays energy proportional to transfer
3. **Energy bonus**: Debtor receives small energy boost (stabilization effect)
4. **Reasonableness bound**: amount ≤ 50 (practical constraint)

## Physical Grounding

- **Energy cost**: From Positive Cost principle - stabilization requires energy
- **Skew conservation**: Total σ is conserved (σ₁' + σ₂' = σ₁ + σ₂)
- **Cascade prevention**: Relieves high-debt states before system collapse

## Connection to virtues.tex

Section 3 (Forgiveness): "To prevent cascade failures from overwhelming debt by
enabling a creditor to cancel a portion of a debtor's curvature."

Key properties:
- `forgiveness_conserves_total_skew`: Total skew unchanged
- `forgiveness_costs_energy`: Creditor pays real cost
- `forgiveness_prevents_collapse`: Can bring debt below threshold

-/

namespace IndisputableMonolith
namespace Ethics
namespace Virtues

open Foundation
open MoralState

/-! ## Core Definition -/

/-- Forgive transfers skew from debtor to creditor with energy exchange.

    The creditor absorbs part of the debtor's negative skew (debt), paying an
    energy penalty. The debtor is relieved and receives a small energy bonus.

    Parameters:
    - creditor: Agent absorbing the debt
    - debtor: Agent being relieved
    - amount: Maximum skew to transfer (capped at 50)
    - h_reasonable: Proof that amount is reasonable (≤ 50)
-/
noncomputable def Forgive
  (creditor debtor : MoralState)
  (amount : ℕ)
  (h_reasonable : amount ≤ 50) :
  MoralState × MoralState :=

  -- Transfer amount is minimum of requested amount and actual debt magnitude
  let transfer_amount := min amount (Int.natAbs debtor.skew)

  -- Energy penalty for creditor (1% per unit transferred)
  let energy_penalty := creditor.energy * (transfer_amount : ℝ) / 100

  -- Energy bonus for debtor (0.5% per unit transferred - stabilization effect)
  let energy_bonus := debtor.energy * (transfer_amount : ℝ) / 200

  -- Create updated creditor state
  let creditor' : MoralState := {
    ledger := creditor.ledger
    agent_bonds := creditor.agent_bonds
    -- Creditor absorbs the debt (skew increases)
    skew := creditor.skew + (transfer_amount : ℤ)
    -- Creditor pays energy cost
    energy := creditor.energy - energy_penalty
    valid := creditor.valid
    energy_pos := by
      have h_transfer_bound : transfer_amount ≤ 50 := by
        unfold transfer_amount
        have : min amount (Int.natAbs debtor.skew) ≤ amount := min_le_left amount _
        omega
      have h_penalty_bound : energy_penalty ≤ creditor.energy / 2 := by
        unfold energy_penalty
        have : (transfer_amount : ℝ) / 100 ≤ 50 / 100 := by
          apply div_le_div_of_nonneg_right
          · norm_cast; exact h_transfer_bound
          · norm_num
        calc
          creditor.energy * (transfer_amount : ℝ) / 100
            ≤ creditor.energy * (50 / 100) := by
              apply mul_le_mul_of_nonneg_left this
              exact le_of_lt creditor.energy_pos
          _ = creditor.energy / 2 := by ring
      linarith [creditor.energy_pos]
  }

  -- Create updated debtor state
  let debtor' : MoralState := {
    ledger := debtor.ledger
    agent_bonds := debtor.agent_bonds
    -- Debtor is relieved of debt (skew decreases in magnitude)
    skew := debtor.skew - (transfer_amount : ℤ)
    -- Debtor receives energy bonus
    energy := debtor.energy + energy_bonus
    valid := debtor.valid
    energy_pos := by
      unfold energy_bonus
      have : 0 < debtor.energy * (transfer_amount : ℝ) / 200 := by
        apply div_pos
        apply mul_pos debtor.energy_pos
        norm_cast
        omega
      linarith [debtor.energy_pos]
  }

  (creditor', debtor')

/-! ## Conservation Theorems -/

/-- Forgiveness conserves total skew -/
theorem forgiveness_conserves_total_skew
  (creditor debtor : MoralState)
  (amount : ℕ)
  (h : amount ≤ 50) :
  let (c', d') := Forgive creditor debtor amount h
  c'.skew + d'.skew = creditor.skew + debtor.skew := by
  unfold Forgive
  simp
  ring

/-- Forgiveness costs the creditor energy -/
theorem forgiveness_costs_energy
  (creditor debtor : MoralState)
  (amount : ℕ)
  (h : amount ≤ 50)
  (h_transfer : 0 < min amount (Int.natAbs debtor.skew)) :
  let (c', d') := Forgive creditor debtor amount h
  c'.energy < creditor.energy := by
  unfold Forgive
  simp
  let transfer_amount := min amount (Int.natAbs debtor.skew)
  let energy_penalty := creditor.energy * (transfer_amount : ℝ) / 100
  have h_penalty_pos : 0 < energy_penalty := by
    unfold energy_penalty transfer_amount
    apply div_pos
    apply mul_pos creditor.energy_pos
    norm_cast
    exact h_transfer
  linarith

/-- Forgiveness benefits the debtor with energy bonus -/
theorem forgiveness_gives_energy_bonus
  (creditor debtor : MoralState)
  (amount : ℕ)
  (h : amount ≤ 50)
  (h_transfer : 0 < min amount (Int.natAbs debtor.skew)) :
  let (c', d') := Forgive creditor debtor amount h
  debtor.energy < d'.energy := by
  unfold Forgive
  simp
  let transfer_amount := min amount (Int.natAbs debtor.skew)
  let energy_bonus := debtor.energy * (transfer_amount : ℝ) / 200
  have h_bonus_pos : 0 < energy_bonus := by
    unfold energy_bonus transfer_amount
    apply div_pos
    apply mul_pos debtor.energy_pos
    norm_cast
    exact h_transfer
  linarith

/-! ## Cascade Prevention -/

/-- Forgiveness can bring debt below threshold -/
theorem forgiveness_prevents_collapse
  (creditor debtor : MoralState)
  (threshold : ℤ)
  (h_debt : threshold < debtor.skew)
  (h_reasonable : (Int.natAbs debtor.skew - Int.natAbs threshold : ℤ) ≤ 10)
  (h_debtor_nonneg : 0 ≤ debtor.skew)
  (h_threshold_nonneg : 0 ≤ threshold) :
  ∃ amount h_bound,
    let (c', d') := Forgive creditor debtor amount h_bound
    d'.skew ≤ threshold := by
  classical
  -- Choose amount equal to the skew difference
  let diff : ℤ := debtor.skew - threshold
  have h_diff_pos : 0 < diff := sub_pos.mpr h_debt
  have h_diff_nonneg : 0 ≤ diff := le_of_lt h_diff_pos
  have h_diff_le : diff ≤ 10 := by
    have := h_reasonable
    simpa [diff, Int.eq_natAbs_of_nonneg h_debtor_nonneg,
      Int.eq_natAbs_of_nonneg h_threshold_nonneg] using this
  let amount : ℕ := Int.toNat diff
  have h_amount_le10 : amount ≤ 10 := by
    have := (Int.toNat_le).2 h_diff_le
    simpa [amount]
  have h_amount_le50 : amount ≤ 50 := le_trans h_amount_le10 (by decide)
  have h_amount_le_skew : amount ≤ Int.natAbs debtor.skew := by
    have h_le : diff ≤ debtor.skew := sub_le_self _ h_threshold_nonneg
    have := Int.toNat_le_toNat h_le
    simpa [amount, Int.natAbs_of_nonneg h_debtor_nonneg]
      using this
  have h_min : min amount (Int.natAbs debtor.skew) = amount :=
    min_eq_left h_amount_le_skew
  have h_amount_cast : (amount : ℤ) = diff := by
    have := Int.ofNat_toNat diff
    simp [amount, diff, h_diff_nonneg] at this
    simpa [amount] using this
  refine ⟨amount, h_amount_le50, ?_⟩
  unfold Forgive
  simp [amount, diff, h_min, h_amount_cast, Int.eq_natAbs_of_nonneg h_debtor_nonneg,
    Int.eq_natAbs_of_nonneg h_threshold_nonneg, sub_eq_add_neg]

/-- Forgiveness is effective for manageable debts -/
theorem forgiveness_effective_for_small_debt
  (creditor debtor : MoralState)
  (h_debt_small : Int.natAbs debtor.skew ≤ 50)
  (h_debtor_nonneg : 0 ≤ debtor.skew) :
  ∃ amount h_bound,
    let (c', d') := Forgive creditor debtor amount h_bound
    d'.skew = 0 := by
  classical
  refine ⟨Int.natAbs debtor.skew, h_debt_small, ?_⟩
  unfold Forgive
  simp [Int.eq_natAbs_of_nonneg h_debtor_nonneg]

/-! ## Energy Economics -/

/-- Energy is not conserved (net loss from transfer friction). -/
theorem forgiveness_net_energy_loss
  (creditor debtor : MoralState)
  (amount : ℕ)
  (h : amount ≤ 50)
  (h_transfer : 0 < min amount (Int.natAbs debtor.skew))
  (h_energy_ratio : debtor.energy < 2 * creditor.energy) :
  let (c', d') := Forgive creditor debtor amount h
  c'.energy + d'.energy < creditor.energy + debtor.energy := by
  classical
  unfold Forgive
  set transfer := min amount (Int.natAbs debtor.skew) with h_transfer_def
  have h_transfer_pos : 0 < (transfer : ℝ) := by exact_mod_cast h_transfer
  have h_transfer_ne : (transfer : ℝ) ≠ 0 := ne_of_gt h_transfer_pos
  have h_factor_pos : 0 < (transfer : ℝ) / 200 := by
    have : (0 : ℝ) < 200 := by norm_num
    exact div_pos h_transfer_pos this
  have h_energy_neg : debtor.energy - 2 * creditor.energy < 0 :=
    sub_neg.mpr h_energy_ratio
  have h_expr :
      debtor.energy * (transfer : ℝ) / 200 -
        creditor.energy * (transfer : ℝ) / 100 =
      (transfer : ℝ) / 200 * (debtor.energy - 2 * creditor.energy) := by
    field_simp [transfer, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, two_mul, h_transfer_ne]
  have h_term_neg :
      (transfer : ℝ) / 200 * (debtor.energy - 2 * creditor.energy) < 0 :=
    mul_neg_of_pos_of_neg h_factor_pos h_energy_neg
  have h_final :
      -creditor.energy * (transfer : ℝ) / 100 + debtor.energy * (transfer : ℝ) / 200 < 0 := by
    simpa [h_expr, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
      using h_term_neg
  simpa [transfer, h_transfer_def, add_comm, add_left_comm, add_assoc, sub_eq_add_neg,
    mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using h_final

/-- The creditor must have sufficient energy to forgive -/
theorem forgiveness_requires_capacity
  (creditor debtor : MoralState)
  (amount : ℕ)
  (h : amount ≤ 50) :
  let transfer_amount := min amount (Int.natAbs debtor.skew)
  let energy_penalty := creditor.energy * (transfer_amount : ℝ) / 100
  energy_penalty < creditor.energy := by
  let transfer_amount := min amount (Int.natAbs debtor.skew)
  have h_bound : transfer_amount ≤ 50 := by
    have : min amount (Int.natAbs debtor.skew) ≤ amount := min_le_left _ _
    omega
  have : (transfer_amount : ℝ) / 100 < 1 := by
    have : (transfer_amount : ℝ) ≤ 50 := by norm_cast; exact h_bound
    linarith
  have : creditor.energy * ((transfer_amount : ℝ) / 100) < creditor.energy * 1 := by
    apply mul_lt_mul_of_pos_left this creditor.energy_pos
  linarith

/-! ## Ethical Properties -/

/-- Forgiveness transfers burden from weak to strong -/
theorem forgiveness_transfers_burden
  (creditor debtor : MoralState)
  (amount : ℕ)
  (h : amount ≤ 50)
  (h_debtor_weak : 0 < debtor.skew) :  -- Debtor has positive skew (debt)
  let (c', d') := Forgive creditor debtor amount h
  c'.skew ≥ creditor.skew ∧ Int.natAbs d'.skew ≤ Int.natAbs debtor.skew := by
  unfold Forgive
  simp
  constructor
  · omega
  · have h_nonneg : 0 ≤ debtor.skew := le_of_lt h_debtor_weak
    have h_transfer_le : min amount (Int.natAbs debtor.skew) ≤ Int.natAbs debtor.skew :=
      min_le_right _ _
    have h_transfer_int_le :
        ((min amount (Int.natAbs debtor.skew) : ℕ) : ℤ) ≤ debtor.skew := by
      have : (min amount (Int.natAbs debtor.skew) : ℕ)
          ≤ Int.natAbs debtor.skew := by exact h_transfer_le
      have h_toNat : (min amount (Int.natAbs debtor.skew) : ℕ) ≤ debtor.skew.toNat := by
        simpa [Int.toNat_of_nonneg h_nonneg, Int.natAbs_of_nonneg h_nonneg] using this
      simpa [Int.toNat_of_nonneg h_nonneg] using Int.ofNat_le.mpr h_toNat
    have h_diff_nonneg :
        0 ≤ debtor.skew - ((min amount (Int.natAbs debtor.skew) : ℕ) : ℤ) :=
      sub_nonneg.mpr h_transfer_int_le
    have h_abs_eq :
        Int.natAbs (debtor.skew - ((min amount (Int.natAbs debtor.skew) : ℕ) : ℤ)) =
          Int.toNat (debtor.skew - ((min amount (Int.natAbs debtor.skew) : ℕ) : ℤ)) :=
      Int.natAbs_of_nonneg h_diff_nonneg
    have h_abs_skew : Int.natAbs debtor.skew = debtor.skew.toNat :=
      Int.natAbs_of_nonneg h_nonneg
    have h_le :
        Int.toNat (debtor.skew - ((min amount (Int.natAbs debtor.skew) : ℕ) : ℤ))
          ≤ debtor.skew.toNat := Int.toNat_le_toNat
        (sub_le_self _ (by exact_mod_cast Nat.zero_le _))
    simpa [h_abs_eq, h_abs_skew]

/-- Forgiveness is bounded (not unlimited) -/
theorem forgiveness_is_bounded
  (creditor debtor : MoralState)
  (amount : ℕ)
  (h : amount ≤ 50) :
  let (c', d') := Forgive creditor debtor amount h
  Int.natAbs (c'.skew - creditor.skew) ≤ 50 := by
  unfold Forgive
  simp
  have : min amount (Int.natAbs debtor.skew) ≤ amount := min_le_left _ _
  omega

/-- Forgiveness can be iterated (multiple applications) -/
theorem forgiveness_compositional
  (creditor debtor : MoralState)
  (amount₁ amount₂ : ℕ)
  (h₁ : amount₁ ≤ 50)
  (h₂ : amount₂ ≤ 50) :
  let (c₁, d₁) := Forgive creditor debtor amount₁ h₁
  let (c₂, d₂) := Forgive c₁ d₁ amount₂ h₂
  c₂.skew + d₂.skew = creditor.skew + debtor.skew := by
  have h1 := forgiveness_conserves_total_skew creditor debtor amount₁ h₁
  have h2 := forgiveness_conserves_total_skew _ _ amount₂ h₂
  unfold Forgive at *
  simp at *
  omega

/-! ## Additional Cascade Metrics -/

lemma forgiveness_debtor_skew_eq
  (creditor debtor : MoralState)
  (amount : ℕ)
  (h : amount ≤ 50) :
  let (c', d') := Forgive creditor debtor amount h
  d'.skew = debtor.skew - (min amount (Int.natAbs debtor.skew) : ℤ) := by
  classical
  unfold Forgive
  simp

lemma forgiveness_creditor_skew_eq
  (creditor debtor : MoralState)
  (amount : ℕ)
  (h : amount ≤ 50) :
  let (c', d') := Forgive creditor debtor amount h
  c'.skew = creditor.skew + (min amount (Int.natAbs debtor.skew) : ℤ) := by
  classical
  unfold Forgive
  simp

lemma forgiveness_debtor_skew_drop
  (creditor debtor : MoralState)
  (amount : ℕ)
  (h : amount ≤ 50) :
  let (c', d') := Forgive creditor debtor amount h
  debtor.skew - d'.skew = (min amount (Int.natAbs debtor.skew) : ℤ) := by
  classical
  unfold Forgive
  simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

lemma forgiveness_creditor_energy_loss
  (creditor debtor : MoralState)
  (amount : ℕ)
  (h : amount ≤ 50) :
  let (c', _) := Forgive creditor debtor amount h
  creditor.energy - c'.energy =
    creditor.energy * (min amount (Int.natAbs debtor.skew) : ℝ) / 100 := by
  classical
  unfold Forgive
  simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

lemma forgiveness_debtor_energy_gain
  (creditor debtor : MoralState)
  (amount : ℕ)
  (h : amount ≤ 50) :
  let (_, d') := Forgive creditor debtor amount h
  d'.energy - debtor.energy =
    debtor.energy * (min amount (Int.natAbs debtor.skew) : ℝ) / 200 := by
  classical
  unfold Forgive
  simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/-! ## ΔS and Consent Integration Hooks -/

namespace Forgiveness

/-! ### Scenario bookkeeping -/

/-- Scenario data required to audit a forgiveness move across ΔS and consent
    pipelines.  The `baseline` ledger is shared by both participants so that the
    eventual `Harm.ActionSpec` can be defined without guessing alignment.

    TODO: Derive this structure directly from ledger projections once the
    ΔS/consent stack provides canonical constructors. -/
structure Scenario where
  creditor : MoralState
  debtor : MoralState
  creditorAgent : AgentId
  debtorAgent : AgentId
  baseline : LedgerState
  amount : ℕ
  amount_le_50 : amount ≤ 50
  creditor_ledger_eq : creditor.ledger = baseline
  debtor_ledger_eq : debtor.ledger = baseline

noncomputable def Scenario.outcome (σ : Scenario) : MoralState × MoralState :=
  Forgive σ.creditor σ.debtor σ.amount σ.amount_le_50

def Scenario.transferAmount (σ : Scenario) : ℕ :=
  min σ.amount (Int.natAbs σ.debtor.skew)

/-- Bonds involved in the forgiveness move (union of creditor and debtor bonds). -/
noncomputable def Scenario.support (σ : Scenario) : Finset BondId :=
  Harm.bondsOfAgent σ.baseline σ.creditorAgent ∪
    Harm.bondsOfAgent σ.baseline σ.debtorAgent

/-- Raw parity pattern used for forgiveness transfers on the selected scope. -/
noncomputable def Scenario.forgivenessMask (σ : Scenario) : BondId → ℝ :=
  PrimitiveLift.assignForgiveness (σ.support)

lemma Scenario.forgivenessMask_zero_of_not_mem
  (σ : Scenario) {b : BondId} (hb : b ∉ σ.support) :
  σ.forgivenessMask b = 0 := by
  classical
  unfold forgivenessMask PrimitiveLift.assignForgiveness PrimitiveLift.maskTo
  simp [hb]

/-- Log-space strain applied per bond for the forgiveness action. -/
noncomputable def Scenario.logStrain (σ : Scenario) : BondId → ℝ :=
  fun b => (σ.transferAmount : ℝ) * σ.forgivenessMask b

lemma Scenario.logStrain_zero_of_not_mem
  (σ : Scenario) {b : BondId} (hb : b ∉ σ.support) :
  σ.logStrain b = 0 := by
  classical
  unfold logStrain
  simp [forgivenessMask_zero_of_not_mem, hb]

/-- Harm action specification induced by a forgiveness move. -/
noncomputable def Scenario.actionSpec (σ : Scenario) : Harm.ActionSpec :=
{ agent := σ.creditorAgent
, support := σ.support
, logStrain := σ.logStrain
, logStrain_zero_of_not_mem := by
    intro b hb
    exact σ.logStrain_zero_of_not_mem hb }

@[simp]
lemma Scenario.actionSpec_agent (σ : Scenario) :
  (σ.actionSpec.agent) = σ.creditorAgent := rfl

/-! ### Harm (ΔS) placeholders -/

/-- Data required to evaluate ΔS once the forgiveness action is expressed as a
    concrete `Harm.ActionSpec`.

    With `Scenario.actionSpec` supplying the canonical action, the remaining
    datum is admissibility of the baseline ledger so that harm lemmas apply. -/
structure DeltaSData (σ : Scenario) where
  baseline_admissible : Foundation.admissible σ.baseline

namespace DeltaSData

variable {σ : Scenario}

/-- Construct ΔS bookkeeping data from an admissible baseline. -/
noncomputable def mk
  (σ : Scenario) (h : Foundation.admissible σ.baseline) : DeltaSData σ :=
{ baseline_admissible := h }

noncomputable def action (data : DeltaSData σ) : Harm.ActionSpec :=
  σ.actionSpec

lemma action_agent (data : DeltaSData σ) :
  (data.action.agent) = σ.creditorAgent := by
  unfold action
  simpa using Scenario.actionSpec_agent σ

noncomputable def debtorHarm (data : DeltaSData σ) : ℝ :=
  Harm.harm σ.creditorAgent σ.debtorAgent (data.action) σ.baseline (data.action_agent)

lemma debtor_harm_nonneg (data : DeltaSData σ) :
  0 ≤ debtorHarm data := by
  simpa [debtorHarm]
    using Harm.harm_nonneg σ.creditorAgent σ.debtorAgent (data.action) σ.baseline
      (data.action_agent) data.baseline_admissible

/-- Aggregate harm over a finite target set.  When the finished ΔS pipeline
    provides precise targets (e.g. debtor plus auditors), this helper will feed
    directly into the minimax harm audit. -/
noncomputable def harmOver
  (data : DeltaSData σ) (targets : Finset AgentId) : ℝ :=
  Harm.harm_over σ.creditorAgent targets (data.action) σ.baseline (data.action_agent)

end DeltaSData

/-! ### Consent scaffolding -/

/-- Witness that the directional derivative used for consent is non-negative.

    Each field mirrors the arguments of `Consent.consent`.  Once the consent
    derivative for forgiveness is implemented, the witness can be constructed
    from the corresponding tangent data. -/
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

def ConsentWitness.consents (w : ConsentWitness) : Prop :=
  Consent.consent w.i w.j w.spec w.distribution w.config w.κ w.hκ w.h_agent
    w.h_prob_mem w.h_prob_pos w.h_support_mem

lemma ConsentWitness.consents_holds (w : ConsentWitness) : w.consents :=
  w.derivative_nonneg

/-- Zero-direction consent witness (derivative exactly zero). -/
noncomputable def ConsentWitness.zero
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
, h_prob_mem := by
    intro pair hp
    cases hp
, h_prob_pos := by
    intro pair hp
    cases hp
, h_support_mem := by
    intro b hb
    cases hb
, derivative_nonneg := by
    have hzero := Consent.directional_derivative_value_zero_spec i j p x κ hκ
    simpa [hzero] using (show 0 ≤ (0 : ℝ) by exact le_of_eq rfl) }

/-- Consent proof obligations for forgiveness.  The actor (creditor) must
    consent to paying the energy cost and the debtor must consent to receiving
    relief under the proposed transfer. -/
structure ConsentData (σ : Scenario) where
  creditorWitness : ConsentWitness
  debtorWitness : ConsentWitness
  creditor_actor_eq : creditorWitness.i = σ.creditorAgent
  creditor_direction_eq : creditorWitness.j = σ.creditorAgent
  debtor_actor_eq : debtorWitness.i = σ.debtorAgent
  debtor_direction_eq : debtorWitness.j = σ.creditorAgent

namespace ConsentData

variable {σ : Scenario}

def respects (data : ConsentData σ) : Prop :=
  data.creditorWitness.consents ∧ data.debtorWitness.consents

lemma respects_holds (data : ConsentData σ) : respects data :=
  ⟨data.creditorWitness.consents_holds, data.debtorWitness.consents_holds⟩

/-- Default consent witnesses obtained from the zero tangent (derivative = 0).

    This is sufficient for current audits; once non-trivial forgiveness tangents
    are available the constructor can be refined without changing downstream
    interfaces. -/
noncomputable def zero
  (σ : Scenario)
  (p : ValueTypes.AgentEnvDistribution)
  (x : ValueTypes.BondConfig)
  (κ : ℝ) (hκ : 0 < κ) : ConsentData σ :=
{ creditorWitness := ConsentWitness.zero σ.creditorAgent σ.creditorAgent p x κ hκ
, debtorWitness := ConsentWitness.zero σ.debtorAgent σ.creditorAgent p x κ hκ
, creditor_actor_eq := rfl
, creditor_direction_eq := rfl
, debtor_actor_eq := rfl
, debtor_direction_eq := rfl }

lemma creditor_consent_statement (data : ConsentData σ) :
  Consent.consent σ.creditorAgent σ.creditorAgent data.creditorWitness.spec
      data.creditorWitness.distribution data.creditorWitness.config
      data.creditorWitness.κ data.creditorWitness.hκ
      (by simpa [data.creditor_direction_eq] using data.creditorWitness.h_agent)
      data.creditorWitness.h_prob_mem data.creditorWitness.h_prob_pos
      data.creditorWitness.h_support_mem := by
  simpa [ConsentWitness.consents, data.creditor_actor_eq,
    data.creditor_direction_eq] using data.creditorWitness.consents_holds

lemma debtor_consent_statement (data : ConsentData σ) :
  Consent.consent σ.debtorAgent σ.creditorAgent data.debtorWitness.spec
      data.debtorWitness.distribution data.debtorWitness.config
      data.debtorWitness.κ data.debtorWitness.hκ
      (by simpa [data.debtor_direction_eq] using data.debtorWitness.h_agent)
      data.debtorWitness.h_prob_mem data.debtorWitness.h_prob_pos
      data.debtorWitness.h_support_mem := by
  simpa [ConsentWitness.consents, data.debtor_actor_eq,
    data.debtor_direction_eq] using data.debtorWitness.consents_holds

end ConsentData

end Forgiveness

end Virtues
end Ethics
end IndisputableMonolith
