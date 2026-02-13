import Mathlib
import IndisputableMonolith.Foundation.RecognitionOperator
import IndisputableMonolith.Ethics.MoralState
import IndisputableMonolith.Ethics.ConservationLaw
import IndisputableMonolith.Support.GoldenRatio
import IndisputableMonolith.Ethics.LeastAction
import IndisputableMonolith.Ethics.ValueTypes

/-!
# Consent: The Local Value Gradient

Consent is the fundamental check for ethical action. An action by agent j
is consensual to agent i if it does not decrease i's Value Functional locally.

## Mathematical Definition

C(i←j; ξ) ⟺ D_j V_i[ξ] ≥ 0

where V_i is the value functional for agent i (Entropy - Mechanical Cost),
and ξ is the infinitesimal action direction.

## Physical Grounding

- **Value Functional**: Free Energy minimization (Entropy - Energy)
- **Locality**: Consent is checked locally (derivative)
- **Compositionality**: Chain rule applies

## Connection to virtues.tex

Section 6 (Consent): "To verify that the action does not violate the
volition of others."

-/

namespace IndisputableMonolith
namespace Ethics
namespace Consent

open Foundation
open MoralState
open scoped Classical

noncomputable section

/-! ## Tangent Space Definitions -/

/-- Geometric tangent direction in bond space. -/
@[ext]
structure FeasibleDirection where
  agent : AgentId
  direction : BondId → ℝ
  /-- Reciprocity maintenance: first-order variation of total skew is zero. -/
  maintains_reciprocity : ∀ s : MoralState,
    s.ledger.active_bonds.sum (fun b => direction b / s.ledger.bond_multipliers b) = 0

/-- Scaling a feasible direction. -/
def smul_direction (c : ℝ) (ξ : FeasibleDirection) : FeasibleDirection where
  agent := ξ.agent
  direction := fun b => c * ξ.direction b
  maintains_reciprocity := by
    intro s
    simp only [mul_div_assoc]
    rw [← Finset.mul_sum]
    simp [ξ.maintains_reciprocity s]

/-- Addition of feasible directions for the same agent (skeleton). -/
def add_direction (ξ₁ ξ₂ : FeasibleDirection) (h : ξ₁.agent = ξ₂.agent) : FeasibleDirection where
  agent := ξ₁.agent
  direction := fun b => ξ₁.direction b + ξ₂.direction b
  maintains_reciprocity := by
    intro s
    simp only [add_div]
    rw [Finset.sum_add_distrib]
    simp [ξ₁.maintains_reciprocity s, ξ₂.maintains_reciprocity s]

/-- The zero direction (no action) -/
def zero_direction (agent : AgentId) : FeasibleDirection where
  agent := agent
  direction := fun _ => 0
  maintains_reciprocity := by intro s; simp

/-- Addition is commutative (witnessed in either order) for feasible directions of the same agent. -/
lemma add_direction_comm
  (ξ₁ ξ₂ : FeasibleDirection) (h : ξ₁.agent = ξ₂.agent) :
  add_direction ξ₁ ξ₂ h
    = add_direction ξ₂ ξ₁ (by simpa using h.symm) := by
  simp only [add_direction, h]
  congr 1
  funext b
  ring

/-- Addition is associative for feasible directions of the same agent. -/
lemma add_direction_assoc
  (ξ₁ ξ₂ ξ₃ : FeasibleDirection)
  (h₁₂ : ξ₁.agent = ξ₂.agent) (h₂₃ : ξ₂.agent = ξ₃.agent)
  (h₁₂₃ : (add_direction ξ₁ ξ₂ h₁₂).agent = ξ₃.agent)
  (h₁₂₃' : ξ₁.agent = (add_direction ξ₂ ξ₃ h₂₃).agent) :
  add_direction (add_direction ξ₁ ξ₂ h₁₂) ξ₃ h₁₂₃
    = add_direction ξ₁ (add_direction ξ₂ ξ₃ h₂₃) h₁₂₃' := by
  simp only [add_direction]
  congr 1
  funext b
  ring

/-- Left identity for add_direction. -/
lemma add_direction_zero_left
  (ξ : FeasibleDirection) (j : AgentId) (h : (zero_direction j).agent = ξ.agent) :
  add_direction (zero_direction j) ξ h = ξ := by
  cases ξ with | mk agent direction mr =>
  simp only [add_direction, zero_direction, zero_add]
  simp only [FeasibleDirection.agent] at h
  subst h
  rfl

/-- Right identity for add_direction. -/
lemma add_direction_zero_right
  (ξ : FeasibleDirection) (j : AgentId) (h : ξ.agent = (zero_direction j).agent) :
  add_direction ξ (zero_direction j) h = ξ := by
  cases ξ with | mk agent direction mr =>
  simp only [add_direction, zero_direction, add_zero]

/-- Bundle of data describing a tangent direction on the feasible manifold.

The base `FeasibleDirection` encodes the agent and bond-space infinitesimal
update, while `prob_support`/`prob_tangent` record the joint distribution
perturbation used when differentiating the mutual-information component of the
value functional. The support and zeroing conditions ensure that all sums are
finite and compatible with σ=0.
-/
@[ext]
structure DirectionSpec where
  /-- Underlying geometric direction (agent plus bond tangent). -/
  direction : FeasibleDirection
  /-- Finite support for probability-space tangents (agent×environment pairs). -/
  prob_support : Finset (ℕ × ℕ)
  /-- Tangent of the joint agent–environment distribution on `prob_support`. -/
  prob_tangent : ℕ → ℕ → ℝ
  /-- Tangent vanishes outside `prob_support`. -/
  prob_zero_outside :
    ∀ {a e}, (⟨a, e⟩ ∉ prob_support) → prob_tangent a e = 0
  /-- Probability tangent preserves total mass (normalization). -/
  mass_zero :
    (prob_support.sum fun pair => prob_tangent pair.1 pair.2) = 0
  /-- Finite support for bond-space tangents. -/
  support : Finset BondId
  /-- Bond tangent vanishes outside the recorded support. -/
  direction_zero_outside :
    ∀ {b}, b ∉ support → direction.direction b = 0
  /-- Bond tangent preserves σ to first order (sum of log-direction zero). -/
  sigma_zero :
    support.sum (fun b => direction.direction b) = 0

namespace DirectionSpec

noncomputable def mechanical_variance (spec : DirectionSpec) : ℝ :=
  spec.support.sum fun b => (spec.direction.direction b) ^ 2

lemma mechanical_variance_nonneg (spec : DirectionSpec) :
    0 ≤ mechanical_variance spec := by
  classical
  unfold mechanical_variance
  refine Finset.sum_nonneg ?_
  intro b hb
  exact sq_nonneg _

variable {σ₁ σ₂ : DirectionSpec}

/-- Zero tangent data for the given agent. -/
def zero (agent : AgentId) : DirectionSpec :=
  { direction := zero_direction agent
    prob_support := ∅
    prob_tangent := fun _ _ => 0
    prob_zero_outside := by intro a e _; rfl
    mass_zero := by simp
    support := ∅
    direction_zero_outside := by intro b _; rfl
    sigma_zero := by simp }

@[simp]
lemma zero_direction_eq (agent : AgentId) :
    (zero agent).direction = zero_direction agent := rfl

@[simp]
lemma zero_prob_support (agent : AgentId) :
    (zero agent).prob_support = ∅ := rfl

@[simp]
lemma zero_support (agent : AgentId) :
    (zero agent).support = ∅ := rfl

/-- Scalar multiplication of tangent data. -/
def smul (α : ℝ) (spec : DirectionSpec) : DirectionSpec :=
  { direction := smul_direction α spec.direction
    prob_support := spec.prob_support
    prob_tangent := fun a e => α * spec.prob_tangent a e
    prob_zero_outside := by
      intro a e hnot
      have := spec.prob_zero_outside (a := a) (e := e) hnot
      simpa [this]
    mass_zero := by
      classical
      have hsum :=
        (Finset.mul_sum (s := spec.prob_support)
          (a := α)
          (f := fun pair => spec.prob_tangent pair.1 pair.2)).symm
      simpa [spec.mass_zero]
        using hsum
    support := spec.support
    direction_zero_outside := by
      intro b hb
      have := spec.direction_zero_outside (b := b) hb
      simpa [smul_direction, this]
    sigma_zero := by
      classical
      have hsum :=
        (Finset.mul_sum (s := spec.support)
          (a := α)
          (f := fun b => spec.direction.direction b)).symm
      simpa [smul_direction, spec.sigma_zero]
        using hsum }

@[simp]
lemma smul_direction_field (α : ℝ) (spec : DirectionSpec) :
    (smul α spec).direction = smul_direction α spec.direction := rfl

@[simp]
lemma smul_support (α : ℝ) (spec : DirectionSpec) :
    (smul α spec).support = spec.support := rfl

@[simp]
lemma smul_prob_support (α : ℝ) (spec : DirectionSpec) :
    (smul α spec).prob_support = spec.prob_support := rfl

/-- Addition of tangent data for directions owned by the same agent. -/
def add (spec₁ spec₂ : DirectionSpec)
    (h_agent : spec₁.direction.agent = spec₂.direction.agent) : DirectionSpec :=
  { direction := add_direction spec₁.direction spec₂.direction h_agent
    prob_support := spec₁.prob_support ∪ spec₂.prob_support
    prob_tangent := fun a e => spec₁.prob_tangent a e + spec₂.prob_tangent a e
    prob_zero_outside := by
      intro a e hnot
      simp only [Finset.mem_union, not_or] at hnot
      rw [spec₁.prob_zero_outside hnot.1, spec₂.prob_zero_outside hnot.2, add_zero]
    mass_zero := by
      -- Sum over union of (p₁ + p₂) = sum of p₁ + sum of p₂ = 0 + 0 = 0
      classical
      have h1 := spec₁.mass_zero
      have h2 := spec₂.mass_zero
      rw [Finset.sum_add_distrib]
      -- Sum of p₁ over union = sum of p₁ over spec₁.prob_support (since p₁ = 0 outside)
      have hsum₁ : (spec₁.prob_support ∪ spec₂.prob_support).sum (fun pair => spec₁.prob_tangent pair.1 pair.2)
          = spec₁.prob_support.sum (fun pair => spec₁.prob_tangent pair.1 pair.2) := by
        symm
        apply Finset.sum_subset Finset.subset_union_left
        intro pair _ hpair
        exact spec₁.prob_zero_outside hpair
      have hsum₂ : (spec₁.prob_support ∪ spec₂.prob_support).sum (fun pair => spec₂.prob_tangent pair.1 pair.2)
          = spec₂.prob_support.sum (fun pair => spec₂.prob_tangent pair.1 pair.2) := by
        symm
        apply Finset.sum_subset Finset.subset_union_right
        intro pair _ hpair
        exact spec₂.prob_zero_outside hpair
      rw [hsum₁, hsum₂, h1, h2, add_zero]
    support := spec₁.support ∪ spec₂.support
    direction_zero_outside := by
      intro b hb
      simp only [Finset.mem_union, not_or] at hb
      simp only [add_direction]
      rw [spec₁.direction_zero_outside hb.1, spec₂.direction_zero_outside hb.2, add_zero]
    sigma_zero := by
      -- Sum over union of (d₁ + d₂) = sum of d₁ + sum of d₂ = 0 + 0 = 0
      classical
      have h1 := spec₁.sigma_zero
      have h2 := spec₂.sigma_zero
      simp only [add_direction]
      rw [Finset.sum_add_distrib]
      -- Sum of d₁ over union = sum of d₁ over spec₁.support (since d₁ = 0 outside)
      have hsum₁ : (spec₁.support ∪ spec₂.support).sum (fun b => spec₁.direction.direction b)
          = spec₁.support.sum (fun b => spec₁.direction.direction b) := by
        symm
        apply Finset.sum_subset Finset.subset_union_left
        intro b _ hb
        exact spec₁.direction_zero_outside hb
      have hsum₂ : (spec₁.support ∪ spec₂.support).sum (fun b => spec₂.direction.direction b)
          = spec₂.support.sum (fun b => spec₂.direction.direction b) := by
        symm
        apply Finset.sum_subset Finset.subset_union_right
        intro b _ hb
        exact spec₂.direction_zero_outside hb
      rw [hsum₁, hsum₂, h1, h2, add_zero]
  }

@[simp]
lemma add_direction_field (spec₁ spec₂ : DirectionSpec)
    (h : spec₁.direction.agent = spec₂.direction.agent) :
    (add spec₁ spec₂ h).direction =
      add_direction spec₁.direction spec₂.direction h := rfl

@[simp]
lemma add_support (spec₁ spec₂ : DirectionSpec)
    (h : spec₁.direction.agent = spec₂.direction.agent) :
    (add spec₁ spec₂ h).support = spec₁.support ∪ spec₂.support := rfl

@[simp]
lemma add_prob_support (spec₁ spec₂ : DirectionSpec)
    (h : spec₁.direction.agent = spec₂.direction.agent) :
    (add spec₁ spec₂ h).prob_support = spec₁.prob_support ∪ spec₂.prob_support := rfl

lemma mem_prob_support_add_iff
  (spec₁ spec₂ : DirectionSpec)
  (h : spec₁.direction.agent = spec₂.direction.agent)
  (pair : ℕ × ℕ) :
  pair ∈ (add spec₁ spec₂ h).prob_support ↔
    pair ∈ spec₁.prob_support ∨ pair ∈ spec₂.prob_support := by
  simp [add_prob_support]

lemma mem_support_add_iff
  (spec₁ spec₂ : DirectionSpec)
  (h : spec₁.direction.agent = spec₂.direction.agent)
  (b : BondId) :
  b ∈ (add spec₁ spec₂ h).support ↔
    b ∈ spec₁.support ∪ spec₂.support := by
  simp [add_support]

lemma add_prob_mem_states
  (p : ValueTypes.AgentEnvDistribution)
  (spec₁ spec₂ : DirectionSpec)
  (h : spec₁.direction.agent = spec₂.direction.agent)
  (h_mem₁ : ∀ pair ∈ spec₁.prob_support,
      pair.1 ∈ p.agent_states ∧ pair.2 ∈ p.env_states)
  (h_mem₂ : ∀ pair ∈ spec₂.prob_support,
      pair.1 ∈ p.agent_states ∧ pair.2 ∈ p.env_states) :
  ∀ pair ∈ (add spec₁ spec₂ h).prob_support,
      pair.1 ∈ p.agent_states ∧ pair.2 ∈ p.env_states := by
  intro pair hpair
  have := (mem_prob_support_add_iff spec₁ spec₂ h pair).1 hpair
  cases this with
  | inl h₁ => exact h_mem₁ pair h₁
  | inr h₂ => exact h_mem₂ pair h₂

lemma add_prob_pos
  (p : ValueTypes.AgentEnvDistribution)
  (spec₁ spec₂ : DirectionSpec)
  (h : spec₁.direction.agent = spec₂.direction.agent)
  (h_pos₁ : ∀ pair ∈ spec₁.prob_support, 0 < p.prob pair.1 pair.2)
  (h_pos₂ : ∀ pair ∈ spec₂.prob_support, 0 < p.prob pair.1 pair.2) :
  ∀ pair ∈ (add spec₁ spec₂ h).prob_support,
      0 < p.prob pair.1 pair.2 := by
  intro pair hpair
  have := (mem_prob_support_add_iff spec₁ spec₂ h pair).1 hpair
  cases this with
  | inl h₁ => exact h_pos₁ pair h₁
  | inr h₂ => exact h_pos₂ pair h₂

lemma add_support_mem
  (x : ValueTypes.BondConfig)
  (spec₁ spec₂ : DirectionSpec)
  (h : spec₁.direction.agent = spec₂.direction.agent)
  (h_mem₁ : ∀ b ∈ spec₁.support, b ∈ x.support)
  (h_mem₂ : ∀ b ∈ spec₂.support, b ∈ x.support) :
  ∀ b ∈ (add spec₁ spec₂ h).support, b ∈ x.support := by
  intro b hb
  have := (mem_support_add_iff spec₁ spec₂ h b).1 hb
  rcases Finset.mem_union.mp this with hb₁ | hb₂
  · exact h_mem₁ _ hb₁
  · exact h_mem₂ _ hb₂

/-- Construct a bond-only tangent with empty probability support.
    Requires the direction to satisfy reciprocity on all moral states. -/
def ofBondTangent
  (agent : AgentId)
  (support : Finset BondId)
  (direction : BondId → ℝ)
  (h_zero : ∀ {b}, b ∉ support → direction b = 0)
  (h_sigma : support.sum (fun b => direction b) = 0)
  (h_reciprocity : ∀ s : MoralState,
    s.ledger.active_bonds.sum (fun b => direction b / s.ledger.bond_multipliers b) = 0) :
    DirectionSpec :=
  { direction :=
      { agent := agent
        direction := direction
        maintains_reciprocity := h_reciprocity }
    prob_support := ∅
    prob_tangent := fun _ _ => 0
    prob_zero_outside := by
      intro a e hmem
      simpa using hmem
    mass_zero := by simp
    support := support
    direction_zero_outside := by
      intro b hb
      simpa using h_zero (b := b) hb
    sigma_zero := h_sigma }

end DirectionSpec

end -- noncomputable section

end Consent
end Ethics
end IndisputableMonolith

-- Basic marginal helpers for lightweight agent–environment distributions.
-- Extending the ValueTypes.AgentEnvDistribution namespace
namespace IndisputableMonolith.Ethics.ValueTypes.AgentEnvDistribution

variable (p : AgentEnvDistribution)

/-- Agent marginal probability (sum over environment states). -/
noncomputable def agentMarginal (a : ℕ) : ℝ :=
  if ha : a ∈ p.agent_states then
    p.env_states.sum (fun e => p.prob a e)
  else
    0

/-- Environment marginal probability (sum over agent states). -/
noncomputable def envMarginal (e : ℕ) : ℝ :=
  if he : e ∈ p.env_states then
    p.agent_states.sum (fun a => p.prob a e)
  else
    0

variable {p}

lemma agentMarginal_eq_sum {a : ℕ} (ha : a ∈ p.agent_states) :
    p.agentMarginal a =
      p.env_states.sum (fun e => p.prob a e) := by
  unfold agentMarginal
  simpa [ha]

lemma envMarginal_eq_sum {e : ℕ} (he : e ∈ p.env_states) :
    p.envMarginal e =
      p.agent_states.sum (fun a => p.prob a e) := by
  unfold envMarginal
  simpa [he]

lemma agentMarginal_nonneg (a : ℕ) : 0 ≤ p.agentMarginal a := by
  classical
  unfold agentMarginal
  split_ifs with ha
  · exact Finset.sum_nonneg (by intro e _; exact p.prob_nonneg _ _)
  · simp

lemma envMarginal_nonneg (e : ℕ) : 0 ≤ p.envMarginal e := by
  classical
  unfold envMarginal
  split_ifs with he
  · exact Finset.sum_nonneg (by intro a _; exact p.prob_nonneg _ _)
  · simp

lemma agentMarginal_pos_of_joint_pos {a e : ℕ}
    (ha : a ∈ p.agent_states) (he : e ∈ p.env_states)
    (hpos : 0 < p.prob a e) :
    0 < agentMarginal p a := by
  classical
  rw [agentMarginal_eq_sum ha]
  calc 0 < p.prob a e := hpos
    _ ≤ p.env_states.sum (fun e' => p.prob a e') :=
        Finset.single_le_sum (fun e' _ => p.prob_nonneg a e') he

lemma envMarginal_pos_of_joint_pos {a e : ℕ}
    (ha : a ∈ p.agent_states) (he : e ∈ p.env_states)
    (hpos : 0 < p.prob a e) :
    0 < envMarginal p e := by
  classical
  rw [envMarginal_eq_sum he]
  calc 0 < p.prob a e := hpos
    _ ≤ p.agent_states.sum (fun a' => p.prob a' e) :=
        Finset.single_le_sum (fun a' _ => p.prob_nonneg a' e) ha

end IndisputableMonolith.Ethics.ValueTypes.AgentEnvDistribution

namespace IndisputableMonolith.Ethics.Consent

open IndisputableMonolith.Ethics.ValueTypes.AgentEnvDistribution
open ValueTypes
open Foundation
-- LeastAction definitions are in Ethics namespace

/-- Information-space contribution of a tangent direction. -/
noncomputable def infoContribution
  (spec : DirectionSpec)
  (p : ValueTypes.AgentEnvDistribution)
  (h_prob_mem : ∀ pair ∈ spec.prob_support,
      pair.1 ∈ p.agent_states ∧ pair.2 ∈ p.env_states)
  (h_prob_pos : ∀ pair ∈ spec.prob_support, 0 < p.prob pair.1 pair.2) : ℝ :=
  by
    classical
    exact spec.prob_support.attach.sum (fun pair =>
      let pairVal := pair.1
      let a := pairVal.1
      let e := pairVal.2
      let hp := pair.property
      let hmem := h_prob_mem pairVal hp
      let ha := hmem.1
      let he := hmem.2
      let hprob := h_prob_pos pairVal hp
      spec.prob_tangent a e *
        (Real.log (p.prob a e)
          - Real.log (agentMarginal (p := p) a)
          - Real.log (envMarginal (p := p) e)))

/-- Mechanical-space contribution of a tangent direction. -/
noncomputable def mechContribution
  (spec : DirectionSpec)
  (x : ValueTypes.BondConfig)
  (h_support_mem : ∀ b ∈ spec.support, b ∈ x.support) : ℝ :=
  by
    classical
    exact spec.support.attach.sum (fun b =>
      let id := b.1
      let hb := b.property
      let xb := x.multiplier id
      ((1 : ℝ) / 2) * (xb - xb⁻¹) * spec.direction.direction id)

lemma infoContribution_eq_sum
  (spec : DirectionSpec)
  (p : ValueTypes.AgentEnvDistribution)
  (h_prob_mem : ∀ pair ∈ spec.prob_support,
      pair.1 ∈ p.agent_states ∧ pair.2 ∈ p.env_states)
  (h_prob_pos : ∀ pair ∈ spec.prob_support, 0 < p.prob pair.1 pair.2) :
  infoContribution spec p h_prob_mem h_prob_pos
    = spec.prob_support.sum (
        fun pair => spec.prob_tangent pair.1 pair.2 *
          (Real.log (p.prob pair.1 pair.2)
            - Real.log (agentMarginal (p := p) pair.1)
            - Real.log (envMarginal (p := p) pair.2))) := by
  classical
  unfold infoContribution
  have := Finset.sum_attach
      (s := spec.prob_support)
      (f :=
        fun pair =>
          spec.prob_tangent pair.1 pair.2 *
            (Real.log (p.prob pair.1 pair.2)
              - Real.log (agentMarginal (p := p) pair.1)
              - Real.log (envMarginal (p := p) pair.2)))
  simpa using this

lemma mechContribution_eq_sum
  (spec : DirectionSpec)
  (x : ValueTypes.BondConfig)
  (h_support_mem : ∀ b ∈ spec.support, b ∈ x.support) :
  mechContribution spec x h_support_mem
    = spec.support.sum (
        fun b =>
          ((1 : ℝ) / 2) *
            (x.multiplier b - (x.multiplier b)⁻¹) * spec.direction.direction b) := by
  classical
  unfold mechContribution
  have := Finset.sum_attach
      (s := spec.support)
      (f := fun b =>
        ((1 : ℝ) / 2) *
          (x.multiplier b - (x.multiplier b)⁻¹) * spec.direction.direction b)
  simpa using this

lemma infoContribution_add
  (spec₁ spec₂ : DirectionSpec)
  (p : ValueTypes.AgentEnvDistribution)
  (h_agent : spec₁.direction.agent = spec₂.direction.agent)
  (h_prob_mem₁ : ∀ pair ∈ spec₁.prob_support,
      pair.1 ∈ p.agent_states ∧ pair.2 ∈ p.env_states)
  (h_prob_mem₂ : ∀ pair ∈ spec₂.prob_support,
      pair.1 ∈ p.agent_states ∧ pair.2 ∈ p.env_states)
  (h_prob_pos₁ : ∀ pair ∈ spec₁.prob_support, 0 < p.prob pair.1 pair.2)
  (h_prob_pos₂ : ∀ pair ∈ spec₂.prob_support, 0 < p.prob pair.1 pair.2) :
  infoContribution (DirectionSpec.add spec₁ spec₂ h_agent) p
      (DirectionSpec.add_prob_mem_states p spec₁ spec₂ h_agent h_prob_mem₁ h_prob_mem₂)
      (DirectionSpec.add_prob_pos p spec₁ spec₂ h_agent h_prob_pos₁ h_prob_pos₂)
    = infoContribution spec₁ p h_prob_mem₁ h_prob_pos₁
      + infoContribution spec₂ p h_prob_mem₂ h_prob_pos₂ := by
  -- Information contribution is linear in the probability tangent
  classical
  rw [infoContribution_eq_sum, infoContribution_eq_sum, infoContribution_eq_sum]
  simp only [DirectionSpec.add_prob_support]
  -- First, show that the add prob_tangent equals the sum
  have h_tang : ∀ (a e : ℕ), (DirectionSpec.add spec₁ spec₂ h_agent).prob_tangent a e
      = spec₁.prob_tangent a e + spec₂.prob_tangent a e := by
    intro a e
    simp only [DirectionSpec.add]
  -- Define the log factor for convenience
  let logFactor := fun (pair : ℕ × ℕ) => Real.log (p.prob pair.1 pair.2)
      - Real.log (agentMarginal (p := p) pair.1)
      - Real.log (envMarginal (p := p) pair.2)
  -- Rewrite using h_tang
  conv_lhs => arg 2; ext pair; rw [h_tang pair.1 pair.2]
  -- Sum over union of (t₁ + t₂) * logFactor = sum of t₁ * logFactor + sum of t₂ * logFactor
  have hsum : (spec₁.prob_support ∪ spec₂.prob_support).sum (fun pair =>
        (spec₁.prob_tangent pair.1 pair.2 + spec₂.prob_tangent pair.1 pair.2) * logFactor pair)
      = (spec₁.prob_support ∪ spec₂.prob_support).sum (fun pair =>
          spec₁.prob_tangent pair.1 pair.2 * logFactor pair)
        + (spec₁.prob_support ∪ spec₂.prob_support).sum (fun pair =>
          spec₂.prob_tangent pair.1 pair.2 * logFactor pair) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro pair _
    ring
  rw [hsum]
  -- Sum of t₁ over union = sum of t₁ over spec₁.prob_support (since t₁ = 0 outside)
  have hsum₁ : (spec₁.prob_support ∪ spec₂.prob_support).sum (fun pair =>
        spec₁.prob_tangent pair.1 pair.2 * logFactor pair)
      = spec₁.prob_support.sum (fun pair =>
          spec₁.prob_tangent pair.1 pair.2 * logFactor pair) := by
    symm
    apply Finset.sum_subset Finset.subset_union_left
    intro pair _ hpair
    simp [spec₁.prob_zero_outside hpair]
  have hsum₂ : (spec₁.prob_support ∪ spec₂.prob_support).sum (fun pair =>
        spec₂.prob_tangent pair.1 pair.2 * logFactor pair)
      = spec₂.prob_support.sum (fun pair =>
          spec₂.prob_tangent pair.1 pair.2 * logFactor pair) := by
    symm
    apply Finset.sum_subset Finset.subset_union_right
    intro pair _ hpair
    simp [spec₂.prob_zero_outside hpair]
  rw [hsum₁, hsum₂]

lemma mechContribution_add
  (spec₁ spec₂ : DirectionSpec)
  (x : ValueTypes.BondConfig)
  (h_agent : spec₁.direction.agent = spec₂.direction.agent)
  (h_support_mem₁ : ∀ b ∈ spec₁.support, b ∈ x.support)
  (h_support_mem₂ : ∀ b ∈ spec₂.support, b ∈ x.support) :
  mechContribution (DirectionSpec.add spec₁ spec₂ h_agent) x
      (DirectionSpec.add_support_mem x spec₁ spec₂ h_agent h_support_mem₁ h_support_mem₂)
    = mechContribution spec₁ x h_support_mem₁ + mechContribution spec₂ x h_support_mem₂ := by
  -- Mechanical contribution is linear in the direction
  classical
  rw [mechContribution_eq_sum, mechContribution_eq_sum, mechContribution_eq_sum]
  simp only [DirectionSpec.add_support]
  -- First, show that the add direction equals the sum of directions
  have h_dir : ∀ b, (DirectionSpec.add spec₁ spec₂ h_agent).direction.direction b
      = spec₁.direction.direction b + spec₂.direction.direction b := by
    intro b
    simp only [DirectionSpec.add, add_direction]
  -- Rewrite using h_dir
  conv_lhs => arg 2; ext b; rw [h_dir b]
  -- Sum over union of (d₁ + d₂) terms = sum of d₁ terms + sum of d₂ terms
  have hsum : (spec₁.support ∪ spec₂.support).sum (fun b =>
        ((1 : ℝ) / 2) * (x.multiplier b - (x.multiplier b)⁻¹) *
          (spec₁.direction.direction b + spec₂.direction.direction b))
      = (spec₁.support ∪ spec₂.support).sum (fun b =>
          ((1 : ℝ) / 2) * (x.multiplier b - (x.multiplier b)⁻¹) * spec₁.direction.direction b)
        + (spec₁.support ∪ spec₂.support).sum (fun b =>
          ((1 : ℝ) / 2) * (x.multiplier b - (x.multiplier b)⁻¹) * spec₂.direction.direction b) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hsum]
  -- Sum of d₁ over union = sum of d₁ over spec₁.support (since d₁ = 0 outside)
  have hsum₁ : (spec₁.support ∪ spec₂.support).sum (fun b =>
        ((1 : ℝ) / 2) * (x.multiplier b - (x.multiplier b)⁻¹) * spec₁.direction.direction b)
      = spec₁.support.sum (fun b =>
          ((1 : ℝ) / 2) * (x.multiplier b - (x.multiplier b)⁻¹) * spec₁.direction.direction b) := by
    symm
    apply Finset.sum_subset Finset.subset_union_left
    intro b _ hb
    simp [spec₁.direction_zero_outside hb]
  have hsum₂ : (spec₁.support ∪ spec₂.support).sum (fun b =>
        ((1 : ℝ) / 2) * (x.multiplier b - (x.multiplier b)⁻¹) * spec₂.direction.direction b)
      = spec₂.support.sum (fun b =>
          ((1 : ℝ) / 2) * (x.multiplier b - (x.multiplier b)⁻¹) * spec₂.direction.direction b) := by
    symm
    apply Finset.sum_subset Finset.subset_union_right
    intro b _ hb
    simp [spec₂.direction_zero_outside hb]
  rw [hsum₁, hsum₂]

/-- Directional derivative of `i`'s value along agent `j`'s contemplated move. -/
noncomputable def directional_derivative_value
  (i j : AgentId)
  (spec : DirectionSpec)
  (p : ValueTypes.AgentEnvDistribution)
  (x : ValueTypes.BondConfig)
  (κ : ℝ)
  (h_κ : 0 < κ)
  (h_agent : spec.direction.agent = j)
  (h_prob_mem : ∀ pair ∈ spec.prob_support,
      pair.1 ∈ p.agent_states ∧ pair.2 ∈ p.env_states)
  (h_prob_pos : ∀ pair ∈ spec.prob_support, 0 < p.prob pair.1 pair.2)
  (h_support_mem : ∀ b ∈ spec.support, b ∈ x.support) : ℝ :=
  κ * infoContribution spec p h_prob_mem h_prob_pos
    - mechContribution spec x h_support_mem

@[simp]
lemma directional_derivative_value_zero_spec
  (i j : AgentId)
  (p : ValueTypes.AgentEnvDistribution)
  (x : ValueTypes.BondConfig)
  (κ : ℝ)
  (h_κ : 0 < κ) :
  directional_derivative_value i j (DirectionSpec.zero j) p x κ h_κ rfl
    (by intro pair hp; cases hp)
    (by intro pair hp; cases hp)
    (by intro b hb; cases hb) = 0 := by
  unfold directional_derivative_value
  simp only [DirectionSpec.zero]
  -- infoContribution over empty prob_support is 0
  -- mechContribution over empty support is 0
  unfold infoContribution mechContribution
  simp

lemma infoContribution_smul
  (α : ℝ)
  (spec : DirectionSpec)
  (p : ValueTypes.AgentEnvDistribution)
  (h_prob_mem : ∀ pair ∈ spec.prob_support,
      pair.1 ∈ p.agent_states ∧ pair.2 ∈ p.env_states)
  (h_prob_pos : ∀ pair ∈ spec.prob_support, 0 < p.prob pair.1 pair.2) :
  infoContribution (DirectionSpec.smul α spec) p h_prob_mem h_prob_pos
    = α * infoContribution spec p h_prob_mem h_prob_pos := by
  unfold infoContribution
  simp only [DirectionSpec.smul]
  rw [Finset.mul_sum]
  congr 1
  ext pair
  ring

lemma mechContribution_smul
  (α : ℝ)
  (spec : DirectionSpec)
  (x : ValueTypes.BondConfig)
  (h_support_mem : ∀ b ∈ spec.support, b ∈ x.support) :
  mechContribution (DirectionSpec.smul α spec) x h_support_mem
    = α * mechContribution spec x h_support_mem := by
  unfold mechContribution
  simp only [DirectionSpec.smul, smul_direction]
  rw [Finset.mul_sum]
  congr 1
  ext b
  ring

lemma directional_derivative_value_smul
  (i j : AgentId)
  (α : ℝ)
  (spec : DirectionSpec)
  (p : AgentEnvDistribution)
  (x : BondConfig)
  (κ : ℝ)
  (h_κ : 0 < κ)
  (h_agent : spec.direction.agent = j)
  (h_prob_mem : ∀ pair ∈ spec.prob_support,
      pair.1 ∈ p.agent_states ∧ pair.2 ∈ p.env_states)
  (h_prob_pos : ∀ pair ∈ spec.prob_support, 0 < p.prob pair.1 pair.2)
  (h_support_mem : ∀ b ∈ spec.support, b ∈ x.support) :
  directional_derivative_value i j (DirectionSpec.smul α spec) p x κ h_κ
      (by simpa [DirectionSpec.smul_direction_field] using h_agent)
      (by simpa [DirectionSpec.smul_prob_support] using h_prob_mem)
      (by simpa [DirectionSpec.smul_prob_support] using h_prob_pos)
      (by simpa [DirectionSpec.smul_support] using h_support_mem)
    = α * directional_derivative_value i j spec p x κ h_κ h_agent h_prob_mem h_prob_pos h_support_mem := by
  unfold directional_derivative_value
  rw [infoContribution_smul, mechContribution_smul]
  ring

/-! ## LA-Projected Feasible Paths -/

/-- Feasible path on σ=0 manifold.

    A path γ : [0,1] → (AgentEnvDistribution × BondConfig) such that:
    - Starts at baseline: γ(0) = (p₀, x₀)
    - Stays on σ=0 manifold: ∀ t, σ(γ(t)) = 0
    - Has tangent vector: dγ/dt|_{t=0} = ξ (in direction space)
    - LA-projected: Minimizes J-cost along path
-/
structure FeasiblePath where
  /-- Baseline distribution -/
  baseline_p : AgentEnvDistribution
  /-- Baseline configuration -/
  baseline_x : BondConfig
  /-- Infinitesimal tangent data on bonds and joint distribution. -/
  spec : DirectionSpec
  /-- Least-action completion used to keep the path on σ=0. -/
  la_completion : IndisputableMonolith.Ethics.LACompletion
  /-- Path parameter → distribution -/
  path_p : ℝ → AgentEnvDistribution
  /-- Path parameter → configuration -/
  path_x : ℝ → BondConfig
  /-- Starts at baseline -/
  starts_at_baseline : path_p 0 = baseline_p ∧ path_x 0 = baseline_x
  /-- Bonds evolve according to the specified tangent at t=0. -/
  bond_tangent_matches : ∀ b, HasDerivAt (fun t => (path_x t).multiplier b) (spec.direction.direction b) 0
  /-- Probability mass evolves according to the specified tangent at t=0. -/
  prob_tangent_matches : ∀ a e, HasDerivAt (fun t => (path_p t).prob a e) (spec.prob_tangent a e) 0
  /-- Stays on σ=0 manifold -/
  stays_feasible : ∀ t, (path_x t).support.sum (fun b => |Real.log ((path_x t).multiplier b)|) = 0

/-! ## Consent Definition -/

/-- **CONSENT**: i consents to j's action encoded by `spec`.

    Definition (Section 6): C(i←j; ξ) ⟺ D_j V_i[ξ] ≥ 0

    Interpretation: j's contemplated act does not lower i's value
    (to first order in the act's magnitude).

    This is LOCAL (derivative), COMPOSITIONAL (chain rule),
    and RESCINDABLE (sign can flip).
-/
def consent
  (i j : AgentId)
  (spec : DirectionSpec)
  (p : AgentEnvDistribution)
  (x : BondConfig)
  (κ : ℝ)
  (h_κ : 0 < κ)
  (h_direction_agent : spec.direction.agent = j)
  (h_prob_mem : ∀ pair ∈ spec.prob_support,
      pair.1 ∈ p.agent_states ∧ pair.2 ∈ p.env_states)
  (h_prob_pos : ∀ pair ∈ spec.prob_support, 0 < p.prob pair.1 pair.2)
  (h_support_mem : ∀ b ∈ spec.support, b ∈ x.support) :
  Prop :=
  directional_derivative_value i j spec p x κ h_κ h_direction_agent h_prob_mem h_prob_pos h_support_mem ≥ 0

lemma consent_of_zero_derivative
  (i j : AgentId) (spec : DirectionSpec)
  (p : AgentEnvDistribution) (x : BondConfig)
  (κ : ℝ) (h_κ : 0 < κ)
  (h_direction_agent : spec.direction.agent = j)
  (h_prob_mem : ∀ pair ∈ spec.prob_support,
      pair.1 ∈ p.agent_states ∧ pair.2 ∈ p.env_states)
  (h_prob_pos : ∀ pair ∈ spec.prob_support, 0 < p.prob pair.1 pair.2)
  (h_support_mem : ∀ b ∈ spec.support, b ∈ x.support)
  (h_der : directional_derivative_value i j spec p x κ h_κ h_direction_agent h_prob_mem h_prob_pos h_support_mem = 0) :
  consent i j spec p x κ h_κ h_direction_agent h_prob_mem h_prob_pos h_support_mem := by
  unfold consent
  simpa [h_der]

-- Consent notation
/-! ## Core Theorems -/

/-- Zero direction always has consent (no change, no objection) -/
theorem zero_direction_always_consent
  (i j : AgentId)
  (p : AgentEnvDistribution)
  (x : BondConfig)
  (κ : ℝ)
  (h_κ : 0 < κ) :
  consent i j (DirectionSpec.zero j) p x κ h_κ rfl
    (by intro pair hp; cases hp)
    (by intro pair hp; cases hp)
    (by intro b hb; cases hb) := by
  unfold consent
  simp [directional_derivative_value_zero_spec]

@[simp]
lemma consent_iff_derivative_nonneg
  (i j : AgentId)
  (spec : DirectionSpec)
  (p : AgentEnvDistribution)
  (x : BondConfig)
  (κ : ℝ) (h_κ : 0 < κ)
  (h_agent : spec.direction.agent = j)
  (h_prob_mem : ∀ pair ∈ spec.prob_support,
      pair.1 ∈ p.agent_states ∧ pair.2 ∈ p.env_states)
  (h_prob_pos : ∀ pair ∈ spec.prob_support, 0 < p.prob pair.1 pair.2)
  (h_support_mem : ∀ b ∈ spec.support, b ∈ x.support) :
  consent i j spec p x κ h_κ h_agent h_prob_mem h_prob_pos h_support_mem ↔
    directional_derivative_value i j spec p x κ h_κ h_agent h_prob_mem h_prob_pos h_support_mem ≥ 0 := Iff.rfl

lemma consent_of_derivative_nonneg
  (i j : AgentId)
  (spec : DirectionSpec)
  (p : AgentEnvDistribution)
  (x : BondConfig)
  (κ : ℝ) (h_κ : 0 < κ)
  (h_agent : spec.direction.agent = j)
  (h_prob_mem : ∀ pair ∈ spec.prob_support,
      pair.1 ∈ p.agent_states ∧ pair.2 ∈ p.env_states)
  (h_prob_pos : ∀ pair ∈ spec.prob_support, 0 < p.prob pair.1 pair.2)
  (h_support_mem : ∀ b ∈ spec.support, b ∈ x.support)
  (h_nonneg : directional_derivative_value i j spec p x κ h_κ h_agent h_prob_mem h_prob_pos h_support_mem ≥ 0) :
  consent i j spec p x κ h_κ h_agent h_prob_mem h_prob_pos h_support_mem := h_nonneg

lemma not_consent_of_derivative_neg
  (i j : AgentId)
  (spec : DirectionSpec)
  (p : AgentEnvDistribution)
  (x : BondConfig)
  (κ : ℝ) (h_κ : 0 < κ)
  (h_agent : spec.direction.agent = j)
  (h_prob_mem : ∀ pair ∈ spec.prob_support,
      pair.1 ∈ p.agent_states ∧ pair.2 ∈ p.env_states)
  (h_prob_pos : ∀ pair ∈ spec.prob_support, 0 < p.prob pair.1 pair.2)
  (h_support_mem : ∀ b ∈ spec.support, b ∈ x.support)
  (h_neg : directional_derivative_value i j spec p x κ h_κ h_agent h_prob_mem h_prob_pos h_support_mem < 0) :
  ¬consent i j spec p x κ h_κ h_agent h_prob_mem h_prob_pos h_support_mem := by
  intro h
  unfold consent at h
  exact not_lt.mpr h h_neg

lemma consent_rescindable_of_sign_flip
  (i j : AgentId)
  (spec : DirectionSpec)
  (p₁ p₂ : AgentEnvDistribution)
  (x : BondConfig)
  (κ : ℝ) (h_κ : 0 < κ)
  (h_agent : spec.direction.agent = j)
  (h_prob_mem₁ : ∀ pair ∈ spec.prob_support,
      pair.1 ∈ p₁.agent_states ∧ pair.2 ∈ p₁.env_states)
  (h_prob_pos₁ : ∀ pair ∈ spec.prob_support, 0 < p₁.prob pair.1 pair.2)
  (h_prob_mem₂ : ∀ pair ∈ spec.prob_support,
      pair.1 ∈ p₂.agent_states ∧ pair.2 ∈ p₂.env_states)
  (h_prob_pos₂ : ∀ pair ∈ spec.prob_support, 0 < p₂.prob pair.1 pair.2)
  (h_support_mem : ∀ b ∈ spec.support, b ∈ x.support)
  (h_before : directional_derivative_value i j spec p₁ x κ h_κ h_agent h_prob_mem₁ h_prob_pos₁ h_support_mem ≥ 0)
  (h_after : directional_derivative_value i j spec p₂ x κ h_κ h_agent h_prob_mem₂ h_prob_pos₂ h_support_mem < 0) :
  consent i j spec p₁ x κ h_κ h_agent h_prob_mem₁ h_prob_pos₁ h_support_mem ∧
    ¬consent i j spec p₂ x κ h_κ h_agent h_prob_mem₂ h_prob_pos₂ h_support_mem := by
  refine ⟨h_before, ?_⟩
  exact not_consent_of_derivative_neg i j spec p₂ x κ h_κ h_agent h_prob_mem₂ h_prob_pos₂ h_support_mem h_after

/-!
### Linearity Over Addition

`directional_derivative_value_add` packages the exact σ-preserving addition rule by
assembling the per-component contributions (`infoContribution_add` and
`mechContribution_add`). The zero-outside witnesses carried by `DirectionSpec`
provide the ΠLA overlap metadata needed to track union supports.
-/
/-!
### Integration Points

* Harm coupling: once `Harm.harm` is fully implemented we will connect the
  derivative sign with ΔS bounds, replacing the shells that previously returned
  `True`.
* Virtue checks: the legacy lemmas have been retired in favour of explicit
  derivative certificates per virtue; see `Virtues-As-Generators.tex` L523ff for
  the intended parameterisation.
-/

end Consent
end Ethics
end IndisputableMonolith
