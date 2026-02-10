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
        have h_transfer_le_50 : (transfer_amount : ℝ) ≤ 50 := by exact_mod_cast h_transfer_bound
        calc creditor.energy * (transfer_amount : ℝ) / 100
            ≤ creditor.energy * 50 / 100 := by
              apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) < 100)
              exact mul_le_mul_of_nonneg_left h_transfer_le_50 (le_of_lt creditor.energy_pos)
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
      have h_bonus_nonneg : 0 ≤ energy_bonus := by
        unfold energy_bonus
        apply div_nonneg
        · apply mul_nonneg (le_of_lt debtor.energy_pos)
          exact_mod_cast Nat.zero_le _
        · norm_num
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
  simp only [Forgive]
  -- c'.skew = creditor.skew + transfer_amount
  -- d'.skew = debtor.skew - transfer_amount
  -- Sum: creditor.skew + transfer_amount + debtor.skew - transfer_amount = creditor.skew + debtor.skew
  ring

/-- Forgiveness costs the creditor energy -/
theorem forgiveness_costs_energy
  (creditor debtor : MoralState)
  (amount : ℕ)
  (h : amount ≤ 50)
  (h_transfer : 0 < min amount (Int.natAbs debtor.skew)) :
  let (c', d') := Forgive creditor debtor amount h
  c'.energy < creditor.energy := by
  simp only [Forgive]
  -- c'.energy = creditor.energy - energy_penalty
  -- energy_penalty = creditor.energy * transfer_amount / 100 > 0
  have h_penalty_pos : 0 < creditor.energy * (min amount (Int.natAbs debtor.skew) : ℝ) / 100 := by
    apply div_pos
    · apply mul_pos creditor.energy_pos
      exact_mod_cast h_transfer
    · norm_num
  linarith

/-- Forgiveness benefits the debtor with energy bonus -/
theorem forgiveness_gives_energy_bonus
  (creditor debtor : MoralState)
  (amount : ℕ)
  (h : amount ≤ 50)
  (h_transfer : 0 < min amount (Int.natAbs debtor.skew)) :
  let (c', d') := Forgive creditor debtor amount h
  debtor.energy < d'.energy := by
  simp only [Forgive]
  -- d'.energy = debtor.energy + energy_bonus
  -- energy_bonus = debtor.energy * transfer_amount / 200 > 0
  have h_bonus_pos : 0 < debtor.energy * (min amount (Int.natAbs debtor.skew) : ℝ) / 200 := by
    apply div_pos
    · apply mul_pos debtor.energy_pos
      exact_mod_cast h_transfer
    · norm_num
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
  -- Use amount = debtor.skew - threshold (the gap)
  -- This is ≤ 10 by h_reasonable, and 10 ≤ 50
  have h_gap_nonneg : 0 ≤ debtor.skew - threshold := by omega
  have h_gap_eq : Int.natAbs (debtor.skew - threshold) = (debtor.skew - threshold).toNat := by
    rw [Int.natAbs_of_nonneg h_gap_nonneg, Int.toNat_of_nonneg h_gap_nonneg]
  have h_gap_le : Int.natAbs (debtor.skew - threshold) ≤ 10 := by
    rw [Int.natAbs_of_nonneg h_debtor_nonneg, Int.natAbs_of_nonneg h_threshold_nonneg] at h_reasonable
    rw [Int.natAbs_of_nonneg h_gap_nonneg]
    have h_sub : debtor.skew - threshold = debtor.skew.toNat - threshold.toNat := by
      rw [Int.toNat_of_nonneg h_debtor_nonneg, Int.toNat_of_nonneg h_threshold_nonneg]
    omega
  use (debtor.skew - threshold).toNat
  use (by omega : (debtor.skew - threshold).toNat ≤ 50)
  simp only [Forgive]
  -- d'.skew = debtor.skew - min (gap.toNat) (natAbs debtor.skew)
  have h_min : min (debtor.skew - threshold).toNat (Int.natAbs debtor.skew) = (debtor.skew - threshold).toNat := by
    apply min_eq_left
    rw [Int.natAbs_of_nonneg h_debtor_nonneg, Int.toNat_of_nonneg h_gap_nonneg]
    omega
  simp only [h_min]
  rw [Int.toNat_of_nonneg h_gap_nonneg]
  omega

/-- Forgiveness is effective for manageable debts -/
theorem forgiveness_effective_for_small_debt
  (creditor debtor : MoralState)
  (h_debt_small : Int.natAbs debtor.skew ≤ 50)
  (h_debtor_nonneg : 0 ≤ debtor.skew) :
  ∃ amount h_bound,
    let (c', d') := Forgive creditor debtor amount h_bound
    d'.skew = 0 := by
  -- Use amount = natAbs debtor.skew, which is ≤ 50
  use Int.natAbs debtor.skew, h_debt_small
  simp only [Forgive]
  -- d'.skew = debtor.skew - min (natAbs debtor.skew) (natAbs debtor.skew)
  --         = debtor.skew - natAbs debtor.skew
  --         = debtor.skew - debtor.skew (since debtor.skew ≥ 0)
  --         = 0
  simp only [min_self]
  rw [Int.natAbs_of_nonneg h_debtor_nonneg]
  omega

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
  simp only [Forgive]
  -- c'.energy = creditor.energy - penalty
  -- d'.energy = debtor.energy + bonus
  -- Sum = creditor.energy + debtor.energy - penalty + bonus
  -- penalty = creditor.energy * t / 100, bonus = debtor.energy * t / 200
  -- Net change = bonus - penalty = debtor.energy * t / 200 - creditor.energy * t / 100
  --            = t * (debtor.energy / 200 - creditor.energy / 100)
  --            = t * (debtor.energy - 2 * creditor.energy) / 200
  -- Since debtor.energy < 2 * creditor.energy, this is negative
  have h_t_pos : (0 : ℝ) < (min amount (Int.natAbs debtor.skew) : ℝ) := by exact_mod_cast h_transfer
  have h_diff_neg : debtor.energy - 2 * creditor.energy < 0 := by linarith
  have h_net_neg : debtor.energy * (min amount (Int.natAbs debtor.skew) : ℝ) / 200 -
      creditor.energy * (min amount (Int.natAbs debtor.skew) : ℝ) / 100 < 0 := by
    have h_eq : debtor.energy * (min amount (Int.natAbs debtor.skew) : ℝ) / 200 -
        creditor.energy * (min amount (Int.natAbs debtor.skew) : ℝ) / 100 =
        (min amount (Int.natAbs debtor.skew) : ℝ) * (debtor.energy - 2 * creditor.energy) / 200 := by ring
    rw [h_eq]
    apply div_neg_of_neg_of_pos
    · exact mul_neg_of_pos_of_neg h_t_pos h_diff_neg
    · norm_num
  linarith

/-- The creditor must have sufficient energy to forgive -/
theorem forgiveness_requires_capacity
  (creditor debtor : MoralState)
  (amount : ℕ)
  (h : amount ≤ 50) :
  let transfer_amount := min amount (Int.natAbs debtor.skew)
  let energy_penalty := creditor.energy * (transfer_amount : ℝ) / 100
  energy_penalty < creditor.energy := by
  have h_energy_pos := creditor.energy_pos
  have h_transfer_le : (min amount (Int.natAbs debtor.skew) : ℝ) ≤ 50 := by
    have h1 : min amount (Int.natAbs debtor.skew) ≤ amount := min_le_left _ _
    calc (min amount (Int.natAbs debtor.skew) : ℝ)
        ≤ (amount : ℝ) := by exact_mod_cast h1
      _ ≤ 50 := by exact_mod_cast h
  have h_ratio_lt_one : (min amount (Int.natAbs debtor.skew) : ℝ) / 100 < 1 := by
    calc (min amount (Int.natAbs debtor.skew) : ℝ) / 100
        ≤ 50 / 100 := by apply div_le_div_of_nonneg_right h_transfer_le; norm_num
      _ = 1 / 2 := by norm_num
      _ < 1 := by norm_num
  calc creditor.energy * (min amount (Int.natAbs debtor.skew) : ℝ) / 100
      = creditor.energy * ((min amount (Int.natAbs debtor.skew) : ℝ) / 100) := by ring
    _ < creditor.energy * 1 := by apply mul_lt_mul_of_pos_left h_ratio_lt_one h_energy_pos
    _ = creditor.energy := by ring

/-! ## Ethical Properties -/

/-- Forgiveness transfers burden from weak to strong -/
theorem forgiveness_transfers_burden
  (creditor debtor : MoralState)
  (amount : ℕ)
  (h : amount ≤ 50)
  (h_debtor_weak : 0 < debtor.skew) :  -- Debtor has positive skew (debt)
  let (c', d') := Forgive creditor debtor amount h
  c'.skew ≥ creditor.skew ∧ Int.natAbs d'.skew ≤ Int.natAbs debtor.skew := by
  simp only [Forgive]
  constructor
  · -- c'.skew = creditor.skew + transfer_amount ≥ creditor.skew
    have h_nonneg : 0 ≤ (min amount (Int.natAbs debtor.skew) : ℤ) := by
      exact_mod_cast Nat.zero_le _
    omega
  · -- |d'.skew| = |debtor.skew - transfer_amount| ≤ |debtor.skew|
    have h_transfer_le : min amount (Int.natAbs debtor.skew) ≤ Int.natAbs debtor.skew :=
      min_le_right _ _
    have h_debtor_nonneg : 0 ≤ debtor.skew := le_of_lt h_debtor_weak
    rw [Int.natAbs_of_nonneg h_debtor_nonneg]
    have h_sub_nonneg : 0 ≤ debtor.skew - (min amount (Int.natAbs debtor.skew) : ℤ) := by
      rw [Int.natAbs_of_nonneg h_debtor_nonneg] at h_transfer_le
      omega
    rw [Int.natAbs_of_nonneg h_sub_nonneg]
    rw [Int.natAbs_of_nonneg h_debtor_nonneg] at h_transfer_le
    omega

/-- Forgiveness is bounded (not unlimited) -/
theorem forgiveness_is_bounded
  (creditor debtor : MoralState)
  (amount : ℕ)
  (h : amount ≤ 50) :
  let (c', d') := Forgive creditor debtor amount h
  Int.natAbs (c'.skew - creditor.skew) ≤ 50 := by
  -- c'.skew = creditor.skew + transfer_amount
  -- c'.skew - creditor.skew = transfer_amount
  -- |transfer_amount| = transfer_amount (since it's non-negative)
  -- transfer_amount ≤ amount ≤ 50
  have h_transfer_bound : min amount (Int.natAbs debtor.skew) ≤ 50 := by
    calc min amount (Int.natAbs debtor.skew)
        ≤ amount := min_le_left amount _
      _ ≤ 50 := h
  simp only [Forgive]
  calc Int.natAbs (creditor.skew + ↑(min amount (Int.natAbs debtor.skew)) - creditor.skew)
      = Int.natAbs (↑(min amount (Int.natAbs debtor.skew)) : ℤ) := by ring_nf
    _ = min amount (Int.natAbs debtor.skew) := Int.natAbs_ofNat _
    _ ≤ 50 := h_transfer_bound

/-- Forgiveness can be iterated (multiple applications) -/
theorem forgiveness_compositional
  (creditor debtor : MoralState)
  (amount₁ amount₂ : ℕ)
  (h₁ : amount₁ ≤ 50)
  (h₂ : amount₂ ≤ 50) :
  let (c₁, d₁) := Forgive creditor debtor amount₁ h₁
  let (c₂, d₂) := Forgive c₁ d₁ amount₂ h₂
  c₂.skew + d₂.skew = creditor.skew + debtor.skew := by
  -- Each Forgive conserves total skew
  have h_cons₁ := forgiveness_conserves_total_skew creditor debtor amount₁ h₁
  simp only [Forgive] at h_cons₁ ⊢
  -- c₁.skew + d₁.skew = creditor.skew + debtor.skew
  -- c₂.skew + d₂.skew = c₁.skew + d₁.skew
  -- Therefore c₂.skew + d₂.skew = creditor.skew + debtor.skew
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
noncomputable def ofAdmissible
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

-- ConsentWitness and ConsentData structures removed due to type complexity
-- with directional_derivative_value. See Ethics/Virtues/Sacrifice.lean for similar reasoning.

end Forgiveness

end Virtues
end Ethics
end IndisputableMonolith
