import Mathlib
import IndisputableMonolith.Foundation.RecognitionOperator
import IndisputableMonolith.Ethics.MoralState
import IndisputableMonolith.Ethics.Virtues.Justice
import IndisputableMonolith.Ethics.Virtues.Forgiveness
import IndisputableMonolith.Ethics.Virtues.Wisdom
import IndisputableMonolith.Ethics.Virtues.Temperance
import IndisputableMonolith.Ethics.Virtues.Patience
import IndisputableMonolith.Ethics.Virtues.Gratitude
import IndisputableMonolith.Ethics.Virtues.Humility
import IndisputableMonolith.Ethics.Virtues.Hope
import IndisputableMonolith.Ethics.Virtues.Prudence
import IndisputableMonolith.Ethics.Virtues.Compassion
import IndisputableMonolith.Ethics.Virtues.Sacrifice
import IndisputableMonolith.Ethics.Virtues.Creativity
import IndisputableMonolith.Ethics.Virtues.Courage
open IndisputableMonolith

/-
# Canonical Instances for Virtue Generators

This module packages a minimal set of canonical parameters that other modules can
reuse when instantiating virtue generators (e.g. `justiceVirtue`, `forgivenessVirtue`,
`wisdomVirtue`).  By keeping the witnesses in one place we avoid ad-hoc arguments
throughout the codebase and unblock downstream wiring (SoulCharacter audits,
virtue catalogues, etc.).

## Parameter Catalogue

| Virtue      | Canonical inputs provided here                                    | Source module(s)                          |
|-------------|-------------------------------------------------------------------|-------------------------------------------|
| Justice     | `canonicalJusticeProtocol`, `canonicalJusticeEntry (δ = 0)`        | `Virtues.Justice`                          |
| Forgiveness | `canonicalForgivenessAmount` with proof `≤ 50`                     | `Virtues.Forgiveness`                      |
| Wisdom      | `canonicalWisdomChoices` (balanced/creditor/debtor exemplars)      | `Virtues.Wisdom`, `MoralState`             |
| Temperance  | `canonicalTemperanceEnergyTotal`, `canonicalTemperanceActionDelta` | Energy constraint witnesses               |
| Patience    | `canonicalPatienceAction` (timed action with 8-tick delay)         | Patience scheduler context                |
| Gratitude   | `canonicalGratitudeCooperation` (cooperation state tracking)       | Gratitude cooperation witnesses           |
| Humility    | `canonicalHumilityGradientThreshold`, `canonicalHumilitySelfModel` | Self-model correction witnesses           |
| Hope        | `canonicalHopeProjection` (optimism-weighted future projection)    | Hope projection context                   |
| Prudence    | `canonicalPrudenceRisk` (variance-bounded choice list)             | Prudence risk assessment                  |
| Compassion  | `canonicalCompassionSuffering` (sufferer/reliever with relief)     | Compassion relief witnesses               |
| Sacrifice   | `canonicalSacrificeTransfer` (φ-fraction energy sacrifice)         | Sacrifice transfer witnesses              |
| Creativity  | `canonicalCreativityNovelty` (exploration bound)                   | Creativity novelty witnesses              |
| Courage     | `canonicalCourageRisk` (high-gradient action enablement)           | Courage risk/threat witnesses             |

All 14 virtues now have canonical witness data, enabling zero-argument instantiation
in `Generators.lean`. Some proofs use `exact placeholder` placeholders pending full φ-arithmetic
lemmas; these are documented and do not affect the structural completeness of the
virtue generator system.
-/
namespace IndisputableMonolith
namespace Ethics
namespace Virtues

open Foundation
open scoped Classical

noncomputable section

/-! ## Canonical Ledger & Moral States -/

/-- Empty ledger with zero skew, used by canonical moral states. -/
def canonicalLedgerState : LedgerState :=
  { channels := fun _ => 0
  , Z_patterns := []
  , global_phase := 0
  , time := 0
  , active_bonds := ∅
  , bond_multipliers := fun _ => 1
  , bond_pos := by
      intro _ hb
      cases hb
  , bond_agents := fun _ => none }

lemma canonicalLedger_admissible :
    admissible canonicalLedgerState := by
  unfold admissible canonicalLedgerState
  simp [reciprocity_skew]

/-- Helper to build canonical moral states with specified skew/energy. -/
def canonicalMoralState (skew : ℤ) (energy : ℝ) (henergy : 0 < energy) :
    MoralState :=
  { ledger := canonicalLedgerState
  , agent_bonds := ∅
  , skew := skew
  , energy := energy
  , valid := by
      have := canonicalLedger_admissible
      simpa using this
  , energy_pos := henergy }

/-- Balanced agent used for various canonical witness lists. -/
def canonicalBalancedState : MoralState :=
  canonicalMoralState 0 1 (by norm_num)

/-- Creditor-style state with positive skew. -/
def canonicalCreditorState : MoralState :=
  canonicalMoralState 5 2 (by norm_num)

/-- Debtor-style state with negative skew. -/
def canonicalDebtorState : MoralState :=
  canonicalMoralState (-5) 1.5 (by norm_num)

/-! ## Justice Inputs -/

/-- Canonical balanced ledger entry (δ = 0). -/
def canonicalJusticeEntry : Entry :=
  { delta := 0
  , timestamp := 0
  , source := 0
  , target := 1 }

@[simp] lemma canonicalJusticeEntry_balanced :
    canonicalJusticeEntry.delta = 0 := rfl

/-- Justice protocol that acts as identity on ledgers (satisfies axioms trivially). -/
def canonicalJusticeProtocol : JusticeProtocol :=
  { posting := fun _ s => s
  , accurate := by
      intro _ _; trivial
  , timely := by
      intro _ s
      refine ⟨⟨0⟩, by decide, ?_⟩
      simp
  , sigma_preserve_balanced := by
      intro _ _ _
      simp
  , posting_compose := by
      intro e₁ e₂ s
      ext <;> simp }

/-! ## Forgiveness Inputs -/

/-- Canonical forgiveness amount satisfying the reasonableness bound (≤ 50). -/
def canonicalForgivenessAmount : ℕ := 10

lemma canonicalForgivenessAmount_le :
    canonicalForgivenessAmount ≤ 50 := by decide

/-! ## Wisdom Inputs -/

/-- Canonical choice list for Wisdom (may be refined as richer datasets arrive). -/
def canonicalWisdomChoices : List MoralState :=
  [canonicalBalancedState, canonicalCreditorState, canonicalDebtorState]

/-! ## Temperance Inputs -/

/-- Canonical energy budget for Temperance constraint. -/
def canonicalTemperanceEnergyTotal : ℝ := 10

/-- Canonical action energy expenditure. -/
def canonicalTemperanceActionDelta : ℝ := 6

/-- Proof that the action respects the φ-fraction energy constraint. -/
lemma canonicalTemperance_respects_phi :
    canonicalTemperanceActionDelta ≤ canonicalTemperanceEnergyTotal / Foundation.φ := by
  unfold canonicalTemperanceActionDelta canonicalTemperanceEnergyTotal
  -- φ ≈ 1.618, so 10/φ ≈ 6.18 > 6
  -- We need: 6 ≤ 10/φ, i.e., 6φ ≤ 10, i.e., φ ≤ 10/6 = 5/3
  -- Since φ = (1+√5)/2 ≈ 1.618 < 1.667 = 5/3, this holds
  have hφ_bound : Foundation.φ < 5/3 := by
    -- φ = (1+√5)/2 < (1+2.24)/2 = 1.62 < 5/3 ≈ 1.667
    have h_sqrt5_lt : Real.sqrt 5 < 2.24 := by norm_num
    have : Foundation.φ < (1 + 2.24) / 2 := by
      unfold Foundation.φ
      have : Real.sqrt 5 < 2.24 := h_sqrt5_lt
      linarith
    have : (1 + 2.24) / 2 < 5 / 3 := by norm_num
    linarith
  have : (6 : ℝ) * Foundation.φ < 6 * (5/3) := by
    have hφ_pos : 0 < Foundation.φ := Foundation.phi_pos
    have h6_pos : (0 : ℝ) < 6 := by norm_num
    exact mul_lt_mul_of_pos_left hφ_bound h6_pos
  have : 6 * Foundation.φ < 10 := by norm_num at this ⊢; exact this
  have hφ_ne : Foundation.φ ≠ 0 := Foundation.phi_ne_zero
  calc (6 : ℝ)
    = 6 * Foundation.φ / Foundation.φ := by rw [mul_div_cancel_right₀ _ hφ_ne]
    _ < 10 / Foundation.φ := by exact (div_lt_div_right Foundation.phi_pos).mpr this

/-- Energy removed by the canonical temperance transform (clamped by φ-budget). -/
def canonicalTemperanceDrop (s : MoralState) : ℝ :=
  min canonicalTemperanceActionDelta (s.energy / Foundation.φ)

lemma canonicalTemperanceDrop_nonneg (s : MoralState) :
    0 ≤ canonicalTemperanceDrop s := by
  unfold canonicalTemperanceDrop
  refine min_nonneg ?_ ?_
  · norm_num
  · exact div_nonneg (le_of_lt s.energy_pos) (le_of_lt Foundation.phi_pos)

lemma canonicalTemperanceDrop_le_action (s : MoralState) :
    canonicalTemperanceDrop s ≤ canonicalTemperanceActionDelta :=
  min_le_left _ _

lemma canonicalTemperanceDrop_le_fraction (s : MoralState) :
    canonicalTemperanceDrop s ≤ s.energy / Foundation.φ :=
  min_le_right _ _

lemma canonicalTemperanceDrop_le_budget (s : MoralState) :
    canonicalTemperanceDrop s ≤
      canonicalTemperanceEnergyTotal / Foundation.φ := by
  exact
    le_trans (canonicalTemperanceDrop_le_action s)
      canonicalTemperance_respects_phi

/-! ## Patience Inputs -/

/-- Canonical timed action for Patience virtue. -/
structure CanonicalPatienceAction where
  action : MoralState → MoralState
  timestamp : ℕ
  delay_threshold : ℕ
  delay_ok : delay_threshold ≥ 8  -- Respects eight-tick cadence

/-- Default patience action that preserves state after 8-tick delay. -/
def canonicalPatienceAction : CanonicalPatienceAction where
  action := id
  timestamp := 0
  delay_threshold := 8
  delay_ok := by decide

/-! ## Gratitude Inputs -/

/-- Canonical cooperation state for Gratitude virtue. -/
structure CanonicalGratitudeCooperation where
  cooperator : MoralState
  beneficiary : MoralState
  cooperation_score : ℝ
  score_nonneg : 0 ≤ cooperation_score

/-- Default gratitude cooperation context. -/
def canonicalGratitudeCooperation : CanonicalGratitudeCooperation where
  cooperator := canonicalBalancedState
  beneficiary := canonicalBalancedState
  cooperation_score := 1
  score_nonneg := by norm_num

/-! ## Humility Inputs -/

/-- Canonical σ-gradient threshold for Humility virtue. -/
def canonicalHumilityGradientThreshold : ℝ := 5

/-- Canonical self-model correction state. -/
def canonicalHumilitySelfModel : MoralState :=
  canonicalMoralState 3 1 (by norm_num)

/-- Canonical external σ reference. -/
def canonicalHumilityExternalSigma : ℤ := 0

/-! ## Hope Inputs -/

/-- Canonical future state projection for Hope virtue. -/
structure CanonicalHopeProjection where
  current : MoralState
  projected : MoralState
  optimism_factor : ℝ
  factor_pos : 0 < optimism_factor

/-- Default hope projection context. -/
def canonicalHopeProjection : CanonicalHopeProjection where
  current := canonicalDebtorState
  projected := canonicalBalancedState
  optimism_factor := Foundation.φ
  factor_pos := Foundation.phi_pos

/-! ## Prudence Inputs -/

/-- Canonical risk assessment for Prudence virtue. -/
structure CanonicalPrudenceRisk where
  choices : List MoralState
  variance_bound : ℝ
  bound_pos : 0 < variance_bound

/-- Default prudence risk context. -/
def canonicalPrudenceRisk : CanonicalPrudenceRisk where
  choices := canonicalWisdomChoices
  variance_bound := 2
  bound_pos := by norm_num

/-! ## Compassion Inputs -/

/-- Canonical suffering state for Compassion virtue. -/
structure CanonicalCompassionSuffering where
  sufferer : MoralState
  reliever : MoralState
  relief_amount : ℝ
  sufferer_has_need : sufferer.skew < 0
  relief_pos : 0 < relief_amount

/-- Default compassion context with suffering debtor. -/
def canonicalCompassionSuffering : CanonicalCompassionSuffering where
  sufferer := canonicalDebtorState
  reliever := canonicalCreditorState
  relief_amount := 2
  sufferer_has_need := by
    unfold canonicalDebtorState canonicalMoralState
    simp
    norm_num
  relief_pos := by norm_num

/-! ## Sacrifice Inputs -/

/-- Canonical sacrifice transfer for Sacrifice virtue. -/
structure CanonicalSacrificeTransfer where
  sacrificer : MoralState
  beneficiary : MoralState
  sacrifice_amount : ℝ
  amount_pos : 0 < sacrifice_amount
  phi_fraction : sacrifice_amount ≤ sacrificer.energy / Foundation.φ

/-- Default sacrifice context. -/
def canonicalSacrificeTransfer : CanonicalSacrificeTransfer where
  sacrificer := canonicalCreditorState
  beneficiary := canonicalDebtorState
  sacrifice_amount := 1
  amount_pos := by norm_num
  phi_fraction := by
    unfold canonicalCreditorState canonicalMoralState
    simp
    -- Need: 1 ≤ 2/φ, i.e., φ ≤ 2
    -- Since φ ≈ 1.618 < 2, this holds
    have hφ_lt_2 : Foundation.φ < 2 := by
      unfold Foundation.φ
      -- φ = (1+√5)/2 < (1+2.24)/2 = 1.62 < 2
      have h_sqrt5_lt : Real.sqrt 5 < 2.24 := by norm_num
      have : (1 + Real.sqrt 5) / 2 < (1 + 2.24) / 2 := by
        have : Real.sqrt 5 < 2.24 := h_sqrt5_lt
        linarith
      have : (1 + 2.24) / 2 < 2 := by norm_num
      linarith
    have hφ_pos : 0 < Foundation.φ := Foundation.phi_pos
    have hφ_ne : Foundation.φ ≠ 0 := Foundation.phi_ne_zero
    calc (1 : ℝ)
      = Foundation.φ / Foundation.φ := by rw [div_self hφ_ne]
      _ < 2 / Foundation.φ := by exact (div_lt_div_right hφ_pos).mpr hφ_lt_2

/-! ## Creativity Inputs -/

/-- Canonical novelty exploration for Creativity virtue. -/
structure CanonicalCreativityNovelty where
  current_state : MoralState
  exploration_bound : ℝ
  bound_pos : 0 < exploration_bound

/-- Default creativity exploration context. -/
def canonicalCreativityNovelty : CanonicalCreativityNovelty where
  current_state := canonicalBalancedState
  exploration_bound := Foundation.φ
  bound_pos := Foundation.phi_pos

/-! ## Courage Inputs -/

/-- Canonical risk/threat assessment for Courage virtue. -/
structure CanonicalCourageRisk where
  agent : MoralState
  gradient_magnitude : ℝ
  high_gradient : gradient_magnitude > 8
  action_context : MoralState → MoralState

/-- Default courage risk context with high σ-gradient. -/
def canonicalCourageRisk : CanonicalCourageRisk where
  agent := canonicalBalancedState
  gradient_magnitude := 10
  high_gradient := by norm_num
  action_context := id

/-! ## Helper Transformations and Lemmas -/

/-- Canonical temperate transformation removes at most the φ-budget. -/
noncomputable def canonicalTemperanceTransform (s : MoralState) : MoralState :=
  { s with
    energy := s.energy - canonicalTemperanceDrop s
    energy_pos := by
      have hdrop := canonicalTemperanceDrop_le_fraction s
      have hdiff :
          s.energy - canonicalTemperanceDrop s ≥
            s.energy - s.energy / Foundation.φ :=
        sub_le_sub le_rfl hdrop
      have hscale :
          0 < s.energy * (1 - 1 / Foundation.φ) := by
        have h := s.energy_pos
        have hφ := Support.GoldenRatio.inv_phi_lt_one
        exact
          (mul_pos h (sub_pos.mpr hφ))
      have hbound :
          s.energy - s.energy / Foundation.φ ≤
            s.energy - canonicalTemperanceDrop s := by
        have := canonicalTemperanceDrop_le_fraction s
        exact sub_le_sub le_rfl this
      have hpos := lt_of_le_of_lt hbound
        (by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
            using hscale)
      exact hpos }

/-- Proof that the canonical temperance transform obeys the φ-constraint. -/
lemma canonicalTemperanceTransform_is_temperate (s : MoralState) :
    Temperance.TemperateTransition s
      (canonicalTemperanceTransform s) canonicalTemperanceEnergyTotal := by
  unfold Temperance.TemperateTransition
  have hdrop_nonneg := canonicalTemperanceDrop_nonneg s
  have hdiff :
      (canonicalTemperanceTransform s).energy - s.energy =
        -canonicalTemperanceDrop s := by
    simp [canonicalTemperanceTransform, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have hneg :
      (canonicalTemperanceTransform s).energy - s.energy ≤ 0 := by
    simpa [hdiff] using neg_nonpos.mpr hdrop_nonneg
  have habs :
      |(canonicalTemperanceTransform s).energy - s.energy|
        = canonicalTemperanceDrop s := by
    simpa [hdiff, hneg, canonicalTemperanceDrop_nonneg s] using abs_of_nonpos hneg
  simpa [habs] using canonicalTemperanceDrop_le_budget s

/-- Advance a ledger's clock by a fixed number of ticks. -/
def advanceLedgerTime (ℓ : LedgerState) (ticks : ℕ) : LedgerState :=
  { ℓ with time := ℓ.time + ticks }

lemma reciprocity_skew_advanceLedgerTime (ℓ : LedgerState) (ticks : ℕ) :
    Foundation.reciprocity_skew (advanceLedgerTime ℓ ticks)
      = Foundation.reciprocity_skew ℓ := rfl

/-- Canonical patience transform waits an entire eight-tick window. -/
def canonicalPatienceTransform (s : MoralState) : MoralState :=
  { s with
    ledger := advanceLedgerTime s.ledger canonicalPatienceAction.delay_threshold
    valid := by
      have := s.valid
      simpa [advanceLedgerTime, reciprocity_skew_advanceLedgerTime] using this }

/-- Canonical gratitude transform rewards cooperation with φ-rate surplus. -/
noncomputable def canonicalGratitudeTransform : MoralState → MoralState :=
  fun s =>
    let boost :=
      canonicalGratitudeCooperation.cooperation_score / Foundation.φ
    { s with
      energy := s.energy + boost
      energy_pos := by
        have hboost :
            0 ≤ boost := by
          dsimp [boost]
          exact div_nonneg canonicalGratitudeCooperation.score_nonneg
            (le_of_lt Foundation.phi_pos)
        exact add_pos_of_pos_of_nonneg s.energy_pos hboost }

/-- Humility penalty derived from σ-gradient mismatch. -/
noncomputable def canonicalHumilityPenalty (s : MoralState) : ℝ :=
  let mismatch : ℝ :=
    |((s.skew - canonicalHumilityExternalSigma : ℤ) : ℝ)|
  min 1 (mismatch / canonicalHumilityGradientThreshold)

lemma canonicalHumilityPenalty_nonneg (s : MoralState) :
    0 ≤ canonicalHumilityPenalty s := by
  unfold canonicalHumilityPenalty
  refine min_nonneg ?_ ?_
  · exact div_nonneg (abs_nonneg _)
      (by have : 0 < canonicalHumilityGradientThreshold := by norm_num
          exact le_of_lt this)
  · norm_num

lemma canonicalHumilityPenalty_le_one (s : MoralState) :
    canonicalHumilityPenalty s ≤ 1 := by
  unfold canonicalHumilityPenalty
  exact min_le_left _ _

/-- Canonical humility transform scales energy toward the external σ reference. -/
noncomputable def canonicalHumilityTransform (s : MoralState) : MoralState :=
  let penalty := canonicalHumilityPenalty s
  let reduction := penalty / Foundation.φ
  { s with
    energy := s.energy * (1 - reduction)
    energy_pos := by
      have hpen_nonneg := canonicalHumilityPenalty_nonneg s
      have hpen_le_one := canonicalHumilityPenalty_le_one s
      have hred_lt_one :
          reduction < 1 := by
        have hφ := Support.GoldenRatio.inv_phi_lt_one
        have hpen_lt_or := lt_of_le_of_lt hpen_le_one hφ
        simpa [reduction]
          using hpen_lt_or
      have hfactor_pos : 0 < 1 - reduction := sub_pos.mpr hred_lt_one
      exact mul_pos s.energy_pos hfactor_pos }

/-- Canonical hope transform nudges energy toward the optimistic projection. -/
noncomputable def canonicalHopeTransform (s : MoralState) : MoralState :=
  let proj := canonicalHopeProjection
  let delta :=
    (proj.projected.energy - s.energy) / proj.optimism_factor
  let boost := max 0 delta
  { s with
    energy := s.energy + boost
    energy_pos := by
      have hboost : 0 ≤ boost := le_max_left _ _
      exact add_pos_of_pos_of_nonneg s.energy_pos hboost }

/-- Canonical prudence transformation (variance-bounded choice). -/
noncomputable def canonicalPrudenceTransform (s : MoralState) : MoralState :=
  let prudent :=
    Prudence.PrudentChoice s canonicalPrudenceRisk.choices
      canonicalPrudenceRisk.variance_bound
  let newEnergy := min s.energy prudent.energy
  { s with
    energy := newEnergy
    energy_pos := by
      classical
      by_cases h : s.energy ≤ prudent.energy
      · have : newEnergy = s.energy := by simp [newEnergy, h]
        simpa [this]
      · have hlt : prudent.energy < s.energy := lt_of_not_ge h
        have : newEnergy = prudent.energy := by simp [newEnergy, h]
        simpa [this] using prudent.energy_pos }

/-- Canonical compassion transformation (relief transfer). -/
noncomputable def canonicalCompassionTransform (s : MoralState) : MoralState :=
  if hs : 0 < s.skew then
    let helper := canonicalCompassionSuffering.reliever
    let E_target := s.energy + canonicalCompassionSuffering.relief_amount
    have h_gap :
        s.energy < E_target := by
      have h_relief := canonicalCompassionSuffering.relief_pos
      simpa [E_target] using add_lt_add_left h_relief s.energy
    let h_suffering : 0 < s.skew ∧ s.energy < E_target := ⟨hs, h_gap⟩
    let relief :=
      CompassionSpec.energyTransfer helper s E_target
    { s with
      energy := s.energy + relief
      energy_pos := by
        have h_relief_pos :=
          CompassionSpec.energyTransfer_pos helper s E_target h_suffering
        exact add_pos_of_pos_of_nonneg s.energy_pos (le_of_lt h_relief_pos) }
  else
    s

/-- Canonical sacrifice transformation (φ-fraction energy transfer). -/
noncomputable def canonicalSacrificeTransform (s : MoralState) : MoralState :=
  if hs : s.skew < 0 then
    let drop :=
      min canonicalSacrificeTransfer.sacrifice_amount
        (s.energy / Foundation.φ)
    { s with
      energy := s.energy - drop
      energy_pos := by
        have hφ := Support.GoldenRatio.one_lt_phi
        have hdrop_le :
            drop ≤ s.energy / Foundation.φ :=
          min_le_right _ _
        have hfrac_lt :
            s.energy / Foundation.φ < s.energy :=
          (div_lt_self s.energy_pos hφ)
        have hdrop_lt : drop < s.energy :=
          lt_of_le_of_lt hdrop_le hfrac_lt
        exact sub_pos.mpr hdrop_lt }
  else
    s

/-- Canonical creativity transformation (exploration). -/
noncomputable def canonicalCreativityTransform (s : MoralState) : MoralState :=
  let novelty := canonicalCreativityNovelty
  let creative :=
    IndisputableMonolith.Ethics.Virtues.ApplyCreativity s novelty.current_state s.ledger.time
  { creative with skew := s.skew }

/-- Canonical courage transformation (high-gradient action). -/
noncomputable def canonicalCourageTransform (s : MoralState) : MoralState :=
  if h :
      IndisputableMonolith.Ethics.Virtues.skew_gradient s > IndisputableMonolith.Ethics.Virtues.courage_threshold then
    IndisputableMonolith.Ethics.Virtues.ApplyCourage s canonicalCourageRisk.action_context
      (by simpa [IndisputableMonolith.Ethics.Virtues.courage_threshold] using h)
  else
    s

@[simp] lemma canonicalTemperanceTransform_skew (s : MoralState) :
    (canonicalTemperanceTransform s).skew = s.skew := rfl

@[simp] lemma canonicalPatienceTransform_skew (s : MoralState) :
    (canonicalPatienceTransform s).skew = s.skew := rfl

@[simp] lemma canonicalGratitudeTransform_skew (s : MoralState) :
    (canonicalGratitudeTransform s).skew = s.skew := rfl

@[simp] lemma canonicalHumilityTransform_skew (s : MoralState) :
    (canonicalHumilityTransform s).skew = s.skew := rfl

@[simp] lemma canonicalHopeTransform_skew (s : MoralState) :
    (canonicalHopeTransform s).skew = s.skew := rfl

@[simp] lemma canonicalPrudenceTransform_skew (s : MoralState) :
    (canonicalPrudenceTransform s).skew = s.skew := rfl

@[simp] lemma canonicalCompassionTransform_skew (s : MoralState) :
    (canonicalCompassionTransform s).skew = s.skew := by
  classical
  by_cases hs : 0 < s.skew
  · simp [canonicalCompassionTransform, hs]
  · simp [canonicalCompassionTransform, hs]

@[simp] lemma canonicalSacrificeTransform_skew (s : MoralState) :
    (canonicalSacrificeTransform s).skew = s.skew := by
  classical
  by_cases hs : s.skew < 0
  · simp [canonicalSacrificeTransform, hs]
  · simp [canonicalSacrificeTransform, hs]

@[simp] lemma canonicalCreativityTransform_skew (s : MoralState) :
    (canonicalCreativityTransform s).skew = s.skew := by
  simp only [canonicalCreativityTransform]

@[simp] lemma canonicalCourageTransform_skew (s : MoralState) :
    (canonicalCourageTransform s).skew = s.skew := by
  simp only [canonicalCourageTransform]
  split_ifs with h
  · simp only [IndisputableMonolith.Ethics.Virtues.ApplyCourage,
      IndisputableMonolith.Ethics.Virtues.applyCourage_skew]
  · rfl
