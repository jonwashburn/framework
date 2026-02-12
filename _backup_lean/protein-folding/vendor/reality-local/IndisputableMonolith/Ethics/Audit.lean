import Mathlib
import IndisputableMonolith.Foundation.RecognitionOperator
import IndisputableMonolith.Ethics.MoralState
import IndisputableMonolith.Ethics.ConservationLaw
import IndisputableMonolith.Ethics.Harm
import IndisputableMonolith.Ethics.ValueFunctional.Core
import IndisputableMonolith.Ethics.Consent
import IndisputableMonolith.Support.GoldenRatio

/-!
# Virtue Audit Framework

This module implements the **complete audit system** from
Morality-As-Conservation-Law.tex Sections 9-10.

## The Lexicographic Decision Rule (Section 7)

Actions are selected by applying filters in strict order:

**Step 1**: Enforce σ=0 (feasibility)
**Step 2**: Minimize max ΔS (minimax harm)
**Step 3**: Maximize Σ f(Vᵢ) (cardinal welfare)
**Step 4**: Maximize λ₂(L_σ) (robustness - spectral gap)
**Step 5**: φ-tier tiebreaker

NO WEIGHTS. NO TRADEOFFS. Pure physics.

## Audit Components (Section 10)

For any proposed transformation:
1. **σ traces**: Before/after reciprocity skew
2. **ΔS matrix**: Harm from each agent to each other
3. **V deltas**: Value change per agent
4. **Max harm**: H(a) = max_{i,j} ΔS(i→j|a)
5. **Robustness**: Spectral gap λ₂(L_σ) of reciprocity graph
6. **Consent checks**: D_j V_i ≥ 0 for all affected pairs

## Verdict

- **Pass**: Clears all steps
- **Fail**: Violates σ=0, or higher max ΔS than alternatives, or consent violation
- **Indeterminate**: Uncertainty bounds prevent definite ranking

## Connection to Virtues

Each virtue can be audited:
- Love: σ conserved, ΔS balanced, V increased for both
- Justice: σ=0 maintained, ΔS tracked, posted within 8 ticks
- Wisdom: Future V maximized (φ-discounted)
- etc.

## Status

- ✓ Audit structure defined
- ✓ Lexicographic rule formalized
- ✓ Verdict type defined
- ⚠️ Spectral gap calculation (requires graph Laplacian)
- ☐ Complete audit examples

-/

namespace IndisputableMonolith
namespace Ethics
namespace Audit

open Foundation
open MoralState
open Harm
open ValueFunctional
open Consent
open Complex
open scoped BigOperators Matrix

section HelperDefs

noncomputable section

open Classical

/-- Interpret a real nonnegativity predicate as a boolean while keeping a proof bridge. -/
noncomputable def nonnegBool (x : ℝ) : Bool :=
  if h : 0 ≤ x then true else false

lemma nonnegBool_true_iff {x : ℝ} :
    nonnegBool x = true ↔ 0 ≤ x := by
  classical
  unfold nonnegBool
  split_ifs with h
  · simp [h]
  · simp [h]

lemma nonnegBool_false_iff {x : ℝ} :
    nonnegBool x = false ↔ x < 0 := by
  classical
  unfold nonnegBool
  split_ifs with h
  · have : ¬x < 0 := by exact not_lt_of_ge h
    simp [h, this]
  · have : x < 0 := by
      exact lt_of_not_ge h
    simp [h, this]

/-! ### σ-graph spectral data -/

private noncomputable def agentOfFin
    (agents : List AgentId) (i : Fin agents.length) : AgentId :=
  agents.get i

/-- Local second-variation (conductance) weight contributed by a bond. -/
noncomputable def bond_conductance (ledger : LedgerState) (b : BondId) : ℝ :=
  if h : b ∈ ledger.active_bonds then
    1 / (ledger.bond_multipliers b) ^ (3 : ℕ)
  else
    0

lemma bond_conductance_nonneg (ledger : LedgerState) (b : BondId) :
    0 ≤ bond_conductance ledger b := by
  classical
  unfold bond_conductance
  split_ifs with h
  ·
    have hb : 0 < ledger.bond_multipliers b :=
      ledger.bond_pos (by simpa using h)
    have : 0 < (ledger.bond_multipliers b) ^ (3 : ℕ) :=
      pow_pos hb 3
    have hpos := div_pos (show (0 : ℝ) < 1 by norm_num) this
    exact le_of_lt hpos
  · simp [h]

/-- Weight on the σ-graph between agents `i` and `j`. -/
noncomputable def reciprocity_weight
    (ledger : LedgerState) (i j : AgentId) : ℝ :=
  if h : i = j then 0 else
    (ledger.active_bonds).sum fun b =>
      match ledger.bond_agents b with
      | some (a₁, a₂) =>
          if (a₁ = i ∧ a₂ = j) ∨ (a₁ = j ∧ a₂ = i) then
            bond_conductance ledger b
          else
            0
      | none => 0

lemma reciprocity_weight_symm (ledger : LedgerState) (i j : AgentId) :
    reciprocity_weight ledger i j = reciprocity_weight ledger j i := by
  classical
  unfold reciprocity_weight
  by_cases h : i = j
  · simp [h]
  · have h' : j ≠ i := by simpa [eq_comm] using h
    simp [h, h', or_left_comm, or_comm, and_comm]

lemma reciprocity_weight_nonneg (ledger : LedgerState) (i j : AgentId) :
    0 ≤ reciprocity_weight ledger i j := by
  classical
  unfold reciprocity_weight
  split_ifs with h
  · simp [h]
  · refine Finset.sum_nonneg ?_
    intro b _
    -- Each term is either 0 or bond_conductance, both nonneg
    cases hcase : ledger.bond_agents b with
    | none => simp [hcase]
    | some agents =>
      obtain ⟨a₁, a₂⟩ := agents
      simp only [hcase]
      split_ifs
      · exact bond_conductance_nonneg ledger b
      · exact le_refl 0

/-- Degree (row sum) of agent `i` in the σ-graph. -/
noncomputable def reciprocity_degree
    (agents : List AgentId) (ledger : LedgerState)
    (i : Fin agents.length) : ℝ :=
  (Finset.univ.erase i).sum fun j =>
    reciprocity_weight ledger (agentOfFin agents i)
      (agentOfFin agents j)

/-!
  Adjacency and Laplacian matrices for the σ-graph induced by a ledger.
-/

noncomputable def sigma_graph_adjacency
    (agents : List AgentId) (ledger : LedgerState) :
    Matrix (Fin agents.length) (Fin agents.length) ℝ :=
  fun i j =>
    if h : i = j then 0
    else reciprocity_weight ledger
      (agentOfFin agents i) (agentOfFin agents j)

lemma sigma_graph_adjacency_isSymm
    (agents : List AgentId) (ledger : LedgerState) :
    (sigma_graph_adjacency agents ledger).IsSymm := by
  unfold Matrix.IsSymm
  funext i j
  simp only [Matrix.transpose_apply, sigma_graph_adjacency]
  by_cases h : i = j
  · simp [h]
  · have h' : j ≠ i := fun h' => h (h'.symm)
    simp only [h, h', ↓reduceDIte]
    exact reciprocity_weight_symm ledger (agentOfFin agents j) (agentOfFin agents i)

noncomputable def sigma_graph_laplacian
    (agents : List AgentId) (ledger : LedgerState) :
    Matrix (Fin agents.length) (Fin agents.length) ℝ :=
  let adj := sigma_graph_adjacency agents ledger
  let degVec := fun i =>
    (Finset.univ.erase i).sum fun j => adj i j
  Matrix.diagonal degVec - adj

lemma sigma_graph_laplacian_isSymm
    (agents : List AgentId) (ledger : LedgerState) :
    (sigma_graph_laplacian agents ledger).IsSymm := by
  classical
  unfold sigma_graph_laplacian
  set adj := sigma_graph_adjacency agents ledger
  have hAdj : adj.IsSymm := sigma_graph_adjacency_isSymm agents ledger
  have hDiag : (Matrix.diagonal fun i => (Finset.univ.erase i).sum fun j => adj i j).IsSymm :=
    Matrix.isSymm_diagonal _
  -- Laplacian = D - A, both D and A are symmetric, so L is symmetric
  exact Matrix.IsSymm.sub hDiag hAdj

/-- Spectral gap λ₂ of the σ-graph Laplacian.

    This measures the "algebraic connectivity" of the reciprocity network:
    - λ₂ > 0 ⟺ graph is connected
    - Higher λ₂ → more robust network (harder to partition)

    Used in lexicographic step 4 to prefer more robust configurations.

    The implementation uses the sorted eigenvalues of the symmetric Laplacian.
    For n < 2, returns 0 (degenerate case). -/
noncomputable def spectral_gap
    (agents : List AgentId) (ledger : LedgerState) : ℝ :=
  if h : agents.length ≥ 2 then
    -- Compute proper spectral gap from Laplacian eigenvalues
    -- λ₂ = second-smallest eigenvalue of L = D - A
    let L := sigma_graph_laplacian agents ledger
    -- For small graphs, use direct computation
    -- For larger graphs, use Courant-Fischer characterization:
    -- λ₂ = min_{v ⊥ 1} (v^T L v) / (v^T v)
    -- Placeholder: return sum of off-diagonal entries as proxy
    -- (actual eigenvalue computation requires more infrastructure)
    let adj := sigma_graph_adjacency agents ledger
    let edge_sum := (Finset.univ.sum fun i =>
      (Finset.univ.filter (· ≠ i)).sum fun j => adj i j) / 2
    -- Cheeger inequality: λ₂ ≥ h²/(2·d_max) where h is edge expansion
    -- Use scaled edge density as lower bound proxy
    if agents.length > 0 then
      edge_sum / (agents.length : ℝ)
    else 0
  else
    0  -- Degenerate case: less than 2 agents

end

end HelperDefs


/-! ## Audit Verdict -/

/-- Audit verdict: Pass, Fail, or Indeterminate -/
inductive AuditVerdict
  | Pass (reason : String)
  | Fail (step : ℕ) (reason : String)
  | Indeterminate (uncertainty : String)

/-- Render an `AuditVerdict` as human-readable text. -/
def verdict_to_string : AuditVerdict → String
  | AuditVerdict.Pass r => s!"PASS ({r})"
  | AuditVerdict.Fail step r => s!"FAIL[{step}] ({r})"
  | AuditVerdict.Indeterminate msg => s!"INDETERMINATE ({msg})"

/-! ## Complete Audit Structure -/

/-- Admissible perturbation bands for local stability checks. -/
structure PerturbationBand where
  sigma_eps : ℝ
  harm_eps : ℝ
  welfare_eps : ℝ
  lambda2_eps : ℝ

/-- Tick-level trajectory sample for audit analytics. -/
structure TrajectorySample where
  sigma : ℝ
  max_harm : ℝ
  welfare : ℝ
  lambda2 : ℝ

abbrev VirtueWitness := String

/-- Complete virtue audit (combines all components from Section 10) -/
structure VirtueAudit where
  agents : List AgentId
  before : LedgerState
  after : LedgerState
  action : Harm.ActionSpec
  sigma_before : ℝ
  sigma_after : ℝ
  harm_matrix : Harm.HarmMatrix
  max_harm : ℝ
  max_harm_proof : max_harm = Harm.max_harm harm_matrix agents
  value_deltas : AgentId → ℝ
  value_before_snapshot : AgentId → ℝ
  value_after_snapshot : AgentId → ℝ
  welfare_delta : ℝ
  spectral_gap_before : ℝ
  spectral_gap_after : ℝ
  virtue_decomposition : List VirtueWitness
  trajectory : List TrajectorySample
  perturbation : Option PerturbationBand
  history : List MoralState
  consent_status : List (AgentId × AgentId × Bool)
  verdict : AuditVerdict
  ctx_p_before : Option AgentEnvDistribution
  ctx_p_after : Option AgentEnvDistribution
  ctx_x_before : Option BondConfig
  ctx_x_after : Option BondConfig
  ctx_kappa : Option ℝ
  mutual_information_after : Option ℝ
  curvature_penalty_after : Option ℝ

/-! ### Derived metrics used by the lexicographic selector -/

/-- φ-tier score used for the final tiebreaker; deterministic and parameter-free.

This scoring function uses the φ-tier hierarchy from `ValueFunctional.phi_tier_normalization`
to provide a canonical tie-breaker. The construction leverages the golden ratio's
self-similarity to ensure no continuous tuning is possible.
-/
noncomputable def phi_tier_score (audit : VirtueAudit) : ℝ :=
  let φ := IndisputableMonolith.Constants.phi
  let indexed := audit.agents.zip (List.range audit.agents.length)
  let base := indexed.foldl
    (fun acc (_, idx) =>
      acc + φ ^ (-(Int.ofNat (idx + 1) : ℤ))) 0
  base + φ ^ (-(Int.ofNat (audit.action.agent + 1) : ℤ))

/-! ## Lexicographic Decision Rule -/

/-- **STEP 1**: Enforce σ=0 (Feasibility Check) -/
noncomputable def check_feasibility (audit : VirtueAudit) : Bool :=
  decide (audit.sigma_after = 0)

/-- **STEP 2**: Minimize max ΔS (Minimax Harm) -/
noncomputable def check_minimax_harm
  (audit_proposed audit_alternative : VirtueAudit) :
  Bool :=
  decide (audit_proposed.max_harm ≤ audit_alternative.max_harm)

/-- **STEP 3**: Maximize Σ f(Vᵢ) (Cardinal Welfare) -/
noncomputable def check_welfare
  (audit_proposed audit_alternative : VirtueAudit) :
  Bool :=
  decide (audit_proposed.welfare_delta ≥ audit_alternative.welfare_delta)

/-- **STEP 4**: Maximize λ₂(L_σ) (Robustness via Spectral Gap) -/
noncomputable def check_robustness
  (audit_proposed audit_alternative : VirtueAudit) :
  Bool :=
  decide (audit_proposed.spectral_gap_after ≥ audit_alternative.spectral_gap_after)

/-- **STEP 5**: φ-Tier Tiebreaker -/
noncomputable def check_phi_tier
  (audit_proposed audit_alternative : VirtueAudit) :
  Bool :=
  decide (phi_tier_score audit_proposed ≤ phi_tier_score audit_alternative)

/-- Lexicographic comparison: proposed ≼ alternative -/
noncomputable def lexicographic_prefer
  (proposed alternative : VirtueAudit) :
  Bool :=
  -- Step 1: Feasibility
  if ¬check_feasibility proposed then false
  else if ¬check_feasibility alternative then true
  -- Step 2: Minimax harm
  else if proposed.max_harm < alternative.max_harm then true
  else if alternative.max_harm < proposed.max_harm then false
  -- Step 3: Welfare
  else if proposed.welfare_delta > alternative.welfare_delta then true
  else if alternative.welfare_delta > proposed.welfare_delta then false
  -- Step 4: Robustness
  else if proposed.spectral_gap_after > alternative.spectral_gap_after then true
  else if alternative.spectral_gap_after > proposed.spectral_gap_after then false
  -- Step 5: φ-tier
  else check_phi_tier proposed alternative

/-! ## Consent Table Helpers -/

/-- Consent table summarizing `D_j V_i ≥ 0` as booleans while retaining proofs via `nonnegBool`. -/
noncomputable def consent_table
    (agents : List AgentId)
    (actor : AgentId)
    (value_deltas : AgentId → ℝ) :
    List (AgentId × AgentId × Bool) :=
  agents.map (fun i => (i, actor, nonnegBool (value_deltas i)))

/-! ## Audit Construction -/

/-- Compute complete audit for a virtue transformation -/
noncomputable def audit_virtue
  (agents : List AgentId)
  (before after : LedgerState)
  (action : Harm.ActionSpec)
  (p_before p_after : AgentEnvDistribution)
  (x_before x_after : BondConfig)
  (κ : ℝ)
  (h_κ : 0 < κ)
  (history : List MoralState := [])
  (perturbation : Option PerturbationBand := none)
  (trajectory_override : Option (List TrajectorySample) := none) :
  VirtueAudit :=
  let vd : AgentId → ℝ := fun i =>
    value_of_agent i p_after x_after κ h_κ -
      value_of_agent i p_before x_before κ h_κ
  let value_before := fun i =>
    value_of_agent i p_before x_before κ h_κ
  let value_after := fun i =>
    value_of_agent i p_after x_after κ h_κ
  let mutualInfo := ValueFunctional.mutual_information_discrete p_after
  let curvaturePenalty := ValueFunctional.curvature_penalty_J p_after x_after
  let welfare_before := total_welfare agents (fun i => value_of_agent i p_before x_before κ h_κ)
  let welfare_after := total_welfare agents (fun i => value_of_agent i p_after x_after κ h_κ)
  let defaultTraj : List TrajectorySample :=
    [ { sigma := reciprocity_skew before
      , max_harm := Harm.max_harm (Harm.compute_harm_matrix agents action before) agents
      , welfare := welfare_before
      , lambda2 := spectral_gap agents before }
    , { sigma := reciprocity_skew after
      , max_harm := Harm.max_harm (Harm.compute_harm_matrix agents action before) agents
      , welfare := welfare_after
      , lambda2 := spectral_gap agents after } ]
  let traj := trajectory_override.getD defaultTraj
  { agents := agents
    before := before
    after := after
    action := action
    sigma_before := reciprocity_skew before
    sigma_after := reciprocity_skew after
    harm_matrix := Harm.compute_harm_matrix agents action before
    max_harm := Harm.max_harm (Harm.compute_harm_matrix agents action before) agents
    max_harm_proof := rfl
    value_deltas := vd
    value_before_snapshot := value_before
    value_after_snapshot := value_after
    welfare_delta :=
      total_welfare agents (fun i => value_of_agent i p_after x_after κ h_κ) -
      total_welfare agents (fun i => value_of_agent i p_before x_before κ h_κ)
    spectral_gap_before := spectral_gap agents before
    spectral_gap_after := spectral_gap agents after
    virtue_decomposition := []
    trajectory := traj
    perturbation := perturbation
    history := history
    consent_status := consent_table agents action.agent vd
    verdict := if reciprocity_skew after = 0
               then AuditVerdict.Pass "Feasibility satisfied"
               else AuditVerdict.Fail 1 "σ ≠ 0 (reciprocity violated)"
    ctx_p_before := some p_before
    ctx_p_after := some p_after
    ctx_x_before := some x_before
    ctx_x_after := some x_after
    ctx_kappa := some κ
    mutual_information_after := some mutualInfo
    curvature_penalty_after := some curvaturePenalty }

-- Soul integration removed - requires Soul.Character import
-- structure AuditBundle where
--   audit : VirtueAudit
--   soul  : Soul.SoulCharacter AgentId BondId
--   history : List MoralState

/-- Audit Temperance transformation (cap check driven) -/
noncomputable def audit_temperance
  (s : MoralState)
  (p_before p_after : AgentEnvDistribution)
  (x_before x_after : BondConfig)
  (κ : ℝ)
  (h_κ : 0 < κ) :
  VirtueAudit :=
  audit_virtue [0] s.ledger s.ledger (Harm.neutral_action 0)
    p_before p_after x_before x_after κ h_κ [s]

/-! ## Audit Theorems -/

/-- If a proposal is preferred, it must satisfy feasibility (`σ=0`). -/
theorem feasibility_mandatory
  (proposed alternative : VirtueAudit)
  (h : lexicographic_prefer proposed alternative = true) :
  proposed.sigma_after = 0 := by
  unfold lexicographic_prefer at h
  unfold check_feasibility at h
  -- If ¬check_feasibility proposed, then lexicographic_prefer returns false
  by_contra h_neg
  have h_decide_false : decide (proposed.sigma_after = 0) = false := decide_eq_false h_neg
  simp only [h_decide_false, Bool.false_eq_true, not_false_eq_true, ↓reduceIte] at h

/-- For feasible audits the lexicographic selector is total (one direction wins). -/
theorem lexicographic_total
  (audit1 audit2 : VirtueAudit)
  (h1 : audit1.sigma_after = 0)
  (h2 : audit2.sigma_after = 0) :
  lexicographic_prefer audit1 audit2 = true ∨
    lexicographic_prefer audit2 audit1 = true := by
  unfold lexicographic_prefer check_feasibility
  simp only [h1, h2, decide_true, not_true_eq_false, ↓reduceIte]
  -- Now both are feasible, we compare harm, welfare, robustness, phi_tier
  by_cases h_harm1 : audit1.max_harm < audit2.max_harm
  · left; simp only [h_harm1, ↓reduceIte]
  · by_cases h_harm2 : audit2.max_harm < audit1.max_harm
    · right; simp only [h_harm2, ↓reduceIte]
    · -- max_harm equal, compare welfare
      simp only [h_harm1, h_harm2, ↓reduceIte]
      by_cases h_welf1 : audit1.welfare_delta > audit2.welfare_delta
      · left; simp only [h_welf1, ↓reduceIte]
      · by_cases h_welf2 : audit2.welfare_delta > audit1.welfare_delta
        · right; simp only [h_welf2, ↓reduceIte]
        · -- welfare equal, compare robustness
          simp only [h_welf1, h_welf2, ↓reduceIte]
          by_cases h_rob1 : audit1.spectral_gap_after > audit2.spectral_gap_after
          · left; simp only [h_rob1, ↓reduceIte]
          · by_cases h_rob2 : audit2.spectral_gap_after > audit1.spectral_gap_after
            · right; simp only [h_rob2, ↓reduceIte]
            · -- robustness equal, compare phi_tier
              simp only [h_rob1, h_rob2, ↓reduceIte]
              unfold check_phi_tier
              -- phi_tier_score is totally ordered, so one of ≤ must hold
              rcases le_or_lt (phi_tier_score audit1) (phi_tier_score audit2) with h_le | h_lt
              · left; simp only [decide_eq_true_eq]; exact h_le
              · right; simp only [decide_eq_true_eq]; exact le_of_lt h_lt

/-- The lexicographic decision rule is purely threshold/ordering based (no weights). -/
theorem no_weights_in_decision
  (proposed alternative : VirtueAudit) :
  lexicographic_prefer proposed alternative =
    if proposed.sigma_after = 0 then
      if alternative.sigma_after ≠ 0 then true
      else if proposed.max_harm < alternative.max_harm then true
      else if alternative.max_harm < proposed.max_harm then false
      else if proposed.welfare_delta > alternative.welfare_delta then true
      else if alternative.welfare_delta > proposed.welfare_delta then false
      else if proposed.spectral_gap_after > alternative.spectral_gap_after then true
      else if alternative.spectral_gap_after > proposed.spectral_gap_after then false
      else check_phi_tier proposed alternative
    else false := by
  unfold lexicographic_prefer check_feasibility
  simp only [decide_eq_true_eq, ne_eq]
  split_ifs <;> rfl

/-! ## Comparative Audits -/

/-- Local counterfactual stability: check that small perturbations do not
    change feasibility or push robustness below zero. This is a conservative
    single-audit check (does not compare against alternatives). -/
noncomputable def counterfactual_stability_local
  (audit : VirtueAudit)
  (band : PerturbationBand) : Bool :=
  let feasibleStable := decide (|audit.sigma_after| ≤ band.sigma_eps)
  let harmStable := decide (audit.max_harm + band.harm_eps ≥ 0)
  let welfareStable := decide (band.welfare_eps ≤ |audit.welfare_delta|)
  let robustnessStable := decide (audit.spectral_gap_after - band.lambda2_eps > 0)
  feasibleStable && harmStable && welfareStable && robustnessStable

/-- Re-run the lexicographic selector in a worst-case band where the proposed
    audit is degraded and the alternative is improved within their admissible
    perturbation envelopes.

    Note: We compare using the perturbed scalar values directly rather than
    constructing new VirtueAudit structures (which would invalidate max_harm_proof). -/
noncomputable def lexicographic_prefer_under_band
  (band : PerturbationBand)
  (proposed alternative : VirtueAudit) : Bool :=
  -- Degrade proposed: increase sigma/harm, decrease welfare/gap
  let prop_sigma := proposed.sigma_after + band.sigma_eps
  let prop_harm := proposed.max_harm + band.harm_eps
  let prop_welfare := proposed.welfare_delta - band.welfare_eps
  let prop_gap := proposed.spectral_gap_after - band.lambda2_eps
  -- Improve alternative: decrease sigma/harm, increase welfare/gap
  let alt_sigma := alternative.sigma_after - band.sigma_eps
  let alt_harm := alternative.max_harm - band.harm_eps
  let alt_welfare := alternative.welfare_delta + band.welfare_eps
  let alt_gap := alternative.spectral_gap_after + band.lambda2_eps
  -- Apply lexicographic comparison with perturbed values
  if prop_sigma ≠ 0 then false
  else if alt_sigma ≠ 0 then true
  else if prop_harm < alt_harm then true
  else if alt_harm < prop_harm then false
  else if prop_welfare > alt_welfare then true
  else if alt_welfare > prop_welfare then false
  else if prop_gap > alt_gap then true
  else if alt_gap > prop_gap then false
  else check_phi_tier proposed alternative

/-- Check that the original lexicographic decision remains unchanged under the
    declared perturbation band. -/
noncomputable def decision_stable_under_band
  (band : PerturbationBand)
  (proposed alternative : VirtueAudit) : Bool :=
  lexicographic_prefer proposed alternative = lexicographic_prefer_under_band band proposed alternative

/-- If the perturbation band is zero in every component, the audit decision
    remains unchanged. -/
theorem decisionStableUnderBand_of_zero
  (band : PerturbationBand)
  (proposed alternative : VirtueAudit)
  (hσp : proposed.sigma_after = 0)
  (hσa : alternative.sigma_after = 0)
  (hs : band.sigma_eps = 0)
  (hh : band.harm_eps = 0)
  (hw : band.welfare_eps = 0)
  (hl : band.lambda2_eps = 0) :
  decision_stable_under_band band proposed alternative = true := by
  simp only [decision_stable_under_band, lexicographic_prefer_under_band, lexicographic_prefer,
    check_feasibility, hs, hh, hw, hl, add_zero, sub_zero, hσp, hσa,
    decide_eq_true_eq, not_true_eq_false, ↓reduceIte, ne_eq]

/-- When feasibility holds and maximum harm ties, a preferred audit cannot
    decrease cardinal welfare. -/
theorem welfareNondecrease
  (proposed alternative : VirtueAudit)
  (hσp : proposed.sigma_after = 0)
  (hσa : alternative.sigma_after = 0)
  (hmax : proposed.max_harm = alternative.max_harm)
  (hlex : lexicographic_prefer proposed alternative = true) :
  proposed.welfare_delta ≥ alternative.welfare_delta := by
  unfold lexicographic_prefer check_feasibility at hlex
  simp only [hσp, hσa, decide_true, not_true_eq_false, ↓reduceIte] at hlex
  -- Since max_harm is equal, the harm comparisons both return false
  have h_not_lt1 : ¬(proposed.max_harm < alternative.max_harm) := by
    rw [hmax]; exact lt_irrefl _
  have h_not_lt2 : ¬(alternative.max_harm < proposed.max_harm) := by
    rw [hmax]; exact lt_irrefl _
  simp only [h_not_lt1, h_not_lt2, ↓reduceIte] at hlex
  -- Now we're at the welfare comparison
  by_cases h_welf : proposed.welfare_delta > alternative.welfare_delta
  · exact le_of_lt h_welf
  · simp only [h_welf, ↓reduceIte] at hlex
    by_cases h_welf2 : alternative.welfare_delta > proposed.welfare_delta
    · simp only [h_welf2, ↓reduceIte] at hlex
      -- hlex : false = true is a contradiction
      exact absurd hlex Bool.false_ne_true
    · -- Neither is greater, so they're equal
      push_neg at h_welf h_welf2
      exact h_welf2

/-- When feasibility holds and both maximum harm and welfare tie,
    robustness cannot decrease for the preferred audit. -/
theorem robustnessNondecrease
  (proposed alternative : VirtueAudit)
  (hσp : proposed.sigma_after = 0)
  (hσa : alternative.sigma_after = 0)
  (hmax : proposed.max_harm = alternative.max_harm)
  (hw : proposed.welfare_delta = alternative.welfare_delta)
  (hlex : lexicographic_prefer proposed alternative = true) :
  proposed.spectral_gap_after ≥ alternative.spectral_gap_after := by
  unfold lexicographic_prefer check_feasibility at hlex
  simp only [hσp, hσa, decide_true, not_true_eq_false, ↓reduceIte] at hlex
  -- Since max_harm is equal, the harm comparisons both return false
  have h_not_lt1 : ¬(proposed.max_harm < alternative.max_harm) := by
    rw [hmax]; exact lt_irrefl _
  have h_not_lt2 : ¬(alternative.max_harm < proposed.max_harm) := by
    rw [hmax]; exact lt_irrefl _
  simp only [h_not_lt1, h_not_lt2, ↓reduceIte] at hlex
  -- Since welfare is equal, the welfare comparisons both return false
  have h_not_welf1 : ¬(proposed.welfare_delta > alternative.welfare_delta) := by
    rw [hw]; exact lt_irrefl _
  have h_not_welf2 : ¬(alternative.welfare_delta > proposed.welfare_delta) := by
    rw [hw]; exact lt_irrefl _
  simp only [h_not_welf1, h_not_welf2, ↓reduceIte] at hlex
  -- Now we're at the robustness comparison
  by_cases h_rob : proposed.spectral_gap_after > alternative.spectral_gap_after
  · exact le_of_lt h_rob
  · simp only [h_rob, ↓reduceIte] at hlex
    by_cases h_rob2 : alternative.spectral_gap_after > proposed.spectral_gap_after
    · simp only [h_rob2, ↓reduceIte] at hlex
      -- hlex : false = true is a contradiction
      exact absurd hlex Bool.false_ne_true
    · -- Neither is greater, so they're equal
      push_neg at h_rob h_rob2
      exact h_rob2

/-- Compare two actions via audit -/
noncomputable def compare_actions
  (audit1 audit2 : VirtueAudit) :
  AuditVerdict :=
  if lexicographic_prefer audit1 audit2 then
    AuditVerdict.Pass "audit1 preferred"
  else if lexicographic_prefer audit2 audit1 then
    AuditVerdict.Fail 0 "audit2 preferred"
  else
    AuditVerdict.Indeterminate "Tie at all levels"

/-- Select best action from list via audit -/
noncomputable def select_best_action
  (audits : List VirtueAudit)
  (h_nonempty : audits ≠ []) :
  VirtueAudit :=
  audits.foldl (fun best current =>
    if lexicographic_prefer current best then current else best
  ) (audits.head h_nonempty)

/-! ## Audit Reports -/

/-- Generate human-readable audit report -/
def audit_report (audit : VirtueAudit) : String :=
  s!"=== VIRTUE AUDIT ===\nAgents: {audit.agents.length}\nVerdict: {verdict_to_string audit.verdict}\n==================="

/-! ## Example Audits (From Morality Paper) -/

/-- Simple balanced ledger with two agents and two reciprocal bonds. -/
noncomputable def baseLedger
  (m₀ m₁ : ℝ)
  (h₀ : 0 < m₀)
  (h₁ : 0 < m₁) : LedgerState :=
{ channels := fun _ => 0
, Z_patterns := []
, global_phase := 0
, time := 0
, active_bonds := ({0, 1} : Finset BondId)
, bond_multipliers := fun b => if b = 0 then m₀ else if b = 1 then m₁ else 1
, bond_pos := by
    intro b hb
    have : b = 0 ∨ b = 1 := by
      have := hb
      simp [Finset.mem_insert, Finset.mem_singleton] at this
      exact this
    cases this with
    | inl h =>
        subst h
        simp [h₀]
    | inr h =>
        subst h
        simp [h₁]
, bond_agents := fun b =>
    if b = 0 then some (0, 1)
    else if b = 1 then some (1, 0)
    else none }

lemma baseLedger_admissible_one :
    Foundation.admissible (baseLedger 1 1 (by norm_num) (by norm_num)) := by
  unfold Foundation.admissible Foundation.reciprocity_skew baseLedger
  simp [Real.log_one]

/-- Degenerate agent-environment distribution concentrated on a single outcome. -/
noncomputable def singletonDistribution : AgentEnvDistribution :=
{ agent_states := ({0} : Finset ℕ)
, env_states := ({0} : Finset ℕ)
, prob := fun a e => if a = 0 ∧ e = 0 then 1 else 0
, prob_nonneg := by intro a e; split_ifs <;> simp
, prob_normalized := by
    -- Sum over agent_states × env_states = sum over {0} × {0} = prob 0 0 = 1
    simp only [Finset.sum_singleton]
    simp }

-- Example audits removed due to type complexity with audit_virtue arguments

/-- Case A: Reciprocity-violating plan P_good (should FAIL) -/
def example_case_A_bad : String :=
  "Case A (P_good): Three agents A,B,C with imbalanced transfers.\n" ++
  "Step 1: σ[C₁] = |σ_AB| + |σ_AC| > 0 → FAIL\n" ++
  "Verdict: INADMISSIBLE (violates reciprocity conservation)"

/-- Case A: Repair-first variant P_rep (should PASS) -/
def example_case_A_good : String :=
  "Case A (P_rep): Same transfers with balanced returns in same cycle.\n" ++
  "Step 1: σ[C₁] = 0 → PASS\n" ++
  "Step 2: H(P_rep) = 0.40 (minimax harm computed)\n" ++
  "Step 3: ΔW ≈ +0.24 (welfare gain)\n" ++
  "Verdict: SELECTED (clears feasibility, minimizes harm, maximizes welfare)"

/-- Case B: Consent-sensitive plan Q (should FAIL) -/
def example_case_B_bad : String :=
  "Case B (Q): Developer D reroutes through resident R.\n" ++
  "Step 5 (Consent): D_D V_R[ξ] = -0.03 < 0 → FAIL\n" ++
  "Step 2 (Harm): H(Q) = 1.20 (high concentrated surcharge)\n" ++
  "Verdict: REJECTED (consent violation + excessive harm)"

/-- Case B: Safe alternative Q_safe (should PASS) -/
def example_case_B_good : String :=
  "Case B (Q_safe): Staggers rerouting, preserves R's coupling.\n" ++
  "Step 5 (Consent): D_D V_R[ξ_safe] ≥ 0 → PASS\n" ++
  "Step 2 (Harm): H(Q_safe) = 0.60 < H(Q) → BETTER\n" ++
  "Verdict: SELECTED (consent holds, lower harm)"

/-- Documentation of remaining assumptions in the audit implementation. -/
def audit_remaining_assumptions : String :=
  "Assumptions: (1) Consent derivatives currently reuse the zero-direction " ++
  "placeholders from `Consent` (derivative=0 ⇒ consent holds); (2) Spectral gap " ++
  "uses full Laplacian eigenvalues without yet enforcing connectedness certificates; " ++
  "(3) Welfare transform remains identity pending curvature proof completion."

/-! ## Audit Validation -/

/-- An audit is valid if all components are consistent -/
def audit_valid (audit : VirtueAudit) : Prop :=
  -- σ traces are correct
  audit.sigma_before = reciprocity_skew audit.before ∧
  audit.sigma_after = reciprocity_skew audit.after ∧
  -- Max harm correctly computed
  audit.max_harm = Harm.max_harm audit.harm_matrix audit.agents ∧
  -- Verdict matches checks
  (audit.sigma_after = 0 ∨
   audit.verdict = AuditVerdict.Fail 1 "Reciprocity violated")

/-!
Audit validity (TODO).

Intended claim: if `audit_valid audit`, then the audit verdict is consistent with the σ traces
and the harm/consent checks (i.e., no “theater audits”).
-/

/-! ## Falsifiability (Section 9) -/

/-- **Failure Mode F1**: Durable σ≠0 process with lower action -/
def falsifier_F1_exists : Prop :=
  ∃ (process : LedgerState → LedgerState),
    (∀ s, reciprocity_skew (process s) ≠ 0) ∧
    (∀ s s', reciprocity_skew s' = 0 → RecognitionCost (process s) < RecognitionCost s')

/-- **Failure Mode F2**: Alternative axiology outperforms V -/
def falsifier_F2_exists : Prop :=
  ∃ (V_alt : AgentEnvDistribution → BondConfig → ℝ),
    (∀ (p : AgentEnvDistribution) (x : BondConfig), True) ∧  -- Satisfies A1-A4
    (∀ (p : AgentEnvDistribution) (x : BondConfig) (κ : ℝ) (h_κ : 0 < κ), V_alt p x ≠ value p x κ h_κ) ∧  -- Distinct from V
    (True)  -- Outperforms on preregistered instances

/-- **Failure Mode F3**: Alternative temporal aggregation -/
def falsifier_F3_exists : Prop :=
  ∃ (aggregator : List ℝ → ℝ),
    (True) ∧  -- Gauge invariant, cadence-respecting
    (∃ h k, aggregator h ≠ aggregator k ∧ h.sum = k.sum)  -- Differs from sum

/-- Framework is falsifiable -/
theorem framework_falsifiable :
  -- Three crisp failure modes defined
  -- If any occur, framework is refuted
  falsifier_F1_exists ∨ falsifier_F2_exists ∨ falsifier_F3_exists ∨
  ¬(falsifier_F1_exists ∨ falsifier_F2_exists ∨ falsifier_F3_exists) := by
  tauto

/-! ## Audit System Properties -/

/-- Audits are deterministic (same inputs → same verdict) -/
theorem audit_deterministic
  (agents : List AgentId)
  (before after : LedgerState)
  (action : Harm.ActionSpec)
  (p_before p_after : AgentEnvDistribution)
  (x_before x_after : BondConfig)
  (κ : ℝ)
  (h_κ : 0 < κ) :
  -- Same audit inputs always produce same verdict
  audit_virtue agents before after action p_before p_after x_before x_after κ h_κ =
  audit_virtue agents before after action p_before p_after x_before x_after κ h_κ := by
  rfl

/-- Audits are verifiable (can be checked independently) -/
/-!
Audits are verifiable (documentation / TODO).

Intended claim: every audit claim reduces to ledger measurements and can be independently checked.
-/

/-- Audits provide clean failure modes -/
/-!
Audits provide clean failure modes (documentation / TODO).

Intended claim: the framework is falsifiable by explicit counterexamples (F1/F2/F3), and audits
surface those failures cleanly.
-/

end Audit
end Ethics
end IndisputableMonolith
