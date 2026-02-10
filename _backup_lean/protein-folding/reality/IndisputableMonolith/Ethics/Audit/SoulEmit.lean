/-!
# Audit → SoulCharacter emission

Concrete oracles projecting fields from MoralState and VirtueAudit and a helper
to emit a SoulCharacter record alongside audit results. This pass avoids new proofs
and uses only data projections available from existing modules.
-/

import IndisputableMonolith.Ethics.MoralState
import IndisputableMonolith.Ethics.Audit
import IndisputableMonolith.Ethics.Soul.Character
import IndisputableMonolith.Ethics.ValueFunctional
import IndisputableMonolith.Ethics.Consent
import IndisputableMonolith.Ethics.Harm
import IndisputableMonolith.Foundation.RecognitionOperator

namespace IndisputableMonolith
namespace Ethics
namespace Audit

open Soul

variable {AgentId BondId : Type}

/-- Default concrete oracles using direct projections. Replace components as richer accessors become available. -/
noncomputable def defaultOracles [DecidableEq AgentId] :
    Soul.CharacterOracles AgentId BondId where
  -- Z-invariant via RecognitionOperator
  zFromMoral := fun moral =>
    Foundation.RecognitionOperator.total_Z moral.ledger
  bondsFromMoral := fun moral =>
    { agentBonds := moral.agent_bonds
    , reciprocityWeight := fun _ => (1.0 : Real) }
  sigmaLedgerFromMoral := fun moral =>
    { sigmaCurrent := moral.skew
    , sigmaDerivative := (0 : Real)
    , sigmaHistory := [] }
  energyFromMoral := fun moral => moral.energy
  -- Consent/harm placeholders for moral-only context (assembler uses audit-based versions below).
  consentFromMoral := fun _moral => fun _i _j => (0 : Real)
  harmFromMoral := fun _moral => fun _i _j => (0 : Real)
  -- Value profile from audit context (per acting agent)
  valueFromAudit := fun audit =>
    let val := audit.value_after_snapshot audit.action.agent
    let mutualInfo :=
      match audit.mutual_information_after with
      | some m => m
      | none =>
          match audit.ctx_p_after with
          | some p => ValueFunctional.mutual_information_discrete p
          | none => (0 : Real)
    let curvaturePenalty :=
      match audit.curvature_penalty_after with
      | some c => c
      | none =>
          match audit.ctx_p_after, audit.ctx_x_after with
          | some p, some x => ValueFunctional.curvature_penalty_J p x
          | _, _ => (0 : Real)
    { value := val, mutualInformation := mutualInfo, curvaturePenalty := curvaturePenalty }
  -- Consent from audit: encode derivative sign proxy (0 if consent holds, −1 otherwise)
  consentFromAudit := fun audit =>
    fun i j =>
      let found := (audit.consent_status.find? (fun t => t.fst = i ∧ t.snd.fst = j)).map (fun t => t.snd.snd)
      match found with
      | some true  => (0 : Real)
      | some false => (-1 : Real)
      | none       => (0 : Real)
  -- Harm kernel from ΔS-matrix
  harmFromAudit := fun audit =>
    fun i j => audit.harm_matrix i j
  virtueSignatureFromAudit := fun audit =>
    { components := audit.virtue_decomposition }
  auditToInvariants := fun audit =>
    { sigmaAfter := audit.sigma_after
    , maxHarm := audit.max_harm
    , welfareDelta := audit.welfare_delta
    , spectralGapAfter := audit.spectral_gap_after
    , phiTier := (0 : Int) }
  robustnessFromAudit := fun audit =>
    { lambda2 := audit.spectral_gap_after }
  trajectoryFromAudit := fun audit =>
    let integralV := audit.trajectory.foldl (fun acc t => acc + t.welfare) 0
    let cumulativeHarm := audit.trajectory.foldl (fun acc t => acc + t.max_harm) 0
    let timeFromHistory :=
      let rec firstBalanced (states : List MoralState) (n : Nat) : Option Nat :=
        match states with
        | [] => none
        | m :: rest =>
            if m.skew = (0 : Int) then some n else firstBalanced rest (n + 1)
      firstBalanced audit.history 0
    let timeToBalance :=
      match timeFromHistory with
      | some n => some n
      | none =>
      let rec firstIdx (xs : List Audit.TrajectorySample) (n : Nat) : Option Nat :=
        match xs with
        | [] => none
        | x :: rest =>
            if x.sigma = 0 then some n else firstIdx rest (n+1)
      firstIdx audit.trajectory 0
    { integralV, cumulativeHarm, timeToBalance }
  trajectoryFromHistory := fun history =>
    let rec firstBalanced : List Ethics.MoralState → Nat → Option Nat
      | [], _ => none
      | s :: rest, n =>
          if s.skew = (0 : Int) then some n else firstBalanced rest (n+1)
    { integralV := (0 : Real)
    , cumulativeHarm := 0
    , timeToBalance := firstBalanced history 0 }
  counterfactualFromAudit := fun audit =>
    let bandVal :=
      match audit.perturbation with
      | some band => band.lambda2_eps
      | none => Real.abs (audit.spectral_gap_after - audit.spectral_gap_before)
    let stable :=
      match audit.perturbation with
      | some band => Audit.counterfactual_stability_local audit band
      | none => true
    { stabilityBand := bandVal
    , decisionUnchanged := stable }
  certificatesFrom := fun _m _a =>
    [ "IndisputableMonolith.Ethics.Consent.consent_iff_derivative_nonneg"
    , "IndisputableMonolith.Ethics.Harm.harm_nonneg"
    , "IndisputableMonolith.Ethics.Virtues.Generators.morality_is_physics"
    , "IndisputableMonolith.Ethics.Audit.lexicographic_prefer" ]

/-- Emit a SoulCharacter from a MoralState and VirtueAudit using `defaultOracles`. -/
noncomputable def emitSoulCharacter [DecidableEq AgentId]
    (moral : Ethics.MoralState)
    (audit : Ethics.Audit.VirtueAudit)
    (history : List Ethics.MoralState := [])
    : Soul.SoulCharacter AgentId BondId :=
  (defaultOracles).assembleFromWithHistory moral audit history

private lemma foldl_welfare_nonneg
  (l : List Audit.TrajectorySample)
  (h : ∀ s ∈ l, 0 ≤ s.welfare) :
  0 ≤ l.foldl (fun acc t => acc + t.welfare) 0 := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
      have hhd : 0 ≤ hd.welfare := h _ (List.mem_cons_self _ _)
      have htl : ∀ s ∈ tl, 0 ≤ s.welfare := by
        intro s hs
        exact h s (List.mem_cons_of_mem _ hs)
      simpa [List.foldl] using add_nonneg hhd (ih htl)

/-- Non-negativity of the default integral when each welfare entry is nonnegative. -/
lemma trajectoryIntegralBound_default
  [DecidableEq AgentId]
  (audit : VirtueAudit)
  (h : ∀ sample ∈ audit.trajectory, 0 ≤ sample.welfare) :
  0 ≤ (defaultOracles.trajectoryFromAudit audit).integralV := by
  classical
  unfold defaultOracles
  simp [foldl_welfare_nonneg, h]

/-- If the first state in history is balanced, the time-to-balance is zero. -/
lemma timeToBalanceCorrect_history_head
  [DecidableEq AgentId]
  {m : MoralState} {rest : List MoralState}
  (audit : VirtueAudit)
  (hHist : audit.history = m :: rest)
  (hSkew : m.skew = 0) :
  (defaultOracles.trajectoryFromAudit audit).timeToBalance = some 0 := by
  classical
  unfold defaultOracles
  simp [hHist, hSkew]

/-- Assemble-and-validate helper using the default oracles. -/
lemma defaultOracles_validAfterAudit
  [DecidableEq AgentId]
  (moral : MoralState)
  (audit : VirtueAudit)
  (h_valid : audit_valid audit)
  (hVerdict : audit.verdict ≠ AuditVerdict.Fail 1 "Reciprocity violated")
  (hH : ∀ i j, 0 ≤ audit.harm_matrix i j)
  (hλ : 0 ≤ audit.spectral_gap_after) :
  Soul.CharacterOracles.Valid ((defaultOracles).assembleFrom moral audit) := by
  classical
  rcases h_valid with ⟨_, hσ_eq, _, hσ_or⟩
  have hσ : audit.sigma_after = 0 := by
    cases hσ_or with
    | inl hs => exact hs
    | inr hv => cases hVerdict hv
  have hσ' :
      (defaultOracles.auditToInvariants audit).sigmaAfter = 0 := by
    simp [defaultOracles, hσ]
  have hH' :
      ∀ i j, 0 ≤ (defaultOracles.harmFromAudit audit) i j := by
    intro i j
    simpa [defaultOracles] using hH i j
  have hλ' :
      0 ≤ (defaultOracles.robustnessFromAudit audit).lambda2 := by
    simpa [defaultOracles] using hλ
  have hE :
      0 < (defaultOracles.energyFromMoral moral) := by
    simpa [defaultOracles] using moral.energy_pos
  exact Soul.CharacterOracles.valid_of_invariants
    defaultOracles moral audit hσ' hH' hλ' hE

end Audit
end Ethics
end IndisputableMonolith
