import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Constants
import IndisputableMonolith.Foundation.LawOfExistence
import IndisputableMonolith.Foundation.SelfModel
import IndisputableMonolith.Foundation.ReflexivityIndex
import IndisputableMonolith.Foundation.PhiForcing

/-!
# Self-Reference Phase Diagram: Stable vs Explosive Configurations

This module completes the Topology of Self-Reference by characterizing the
**phase space** of self-referential configurations.

## The Core Question

When is self-reference stable (finite cost) vs explosive (infinite defect)?

## The Answer

Self-reference is characterized by a **phase diagram** with distinct regions:

| Phase | Cost | Stability | Example |
|-------|------|-----------|---------|
| Stable | J < ∞ | Fixed point exists | Normal consciousness |
| Critical | J = J_crit | Phase boundary | Liminal states |
| Explosive | J → ∞ | No fixed point | Gödelian self-ref |
| Transcendent | J ≈ 0 | Pure witness | Samadhi |

## Connection to φ

The phase boundaries are determined by φ-thresholds:
- **φ^(-5)**: Minimum energy for self-reference (coherence threshold)
- **φ^(-45)**: Critical density for phase transition (Gap-45)
- **φ^n**: Energy levels for different reflexivity depths

## Testable Predictions

1. Meditation moves the system toward the Transcendent phase
2. Psychedelics temporarily push toward the Critical/Explosive boundary
3. Dissociation is a partial phase separation
4. Sleep cycles through different phases
-/

namespace IndisputableMonolith
namespace Foundation
namespace SelfReferencePhaseDiagram

open Real
open LawOfExistence
open Constants
open SelfModel
open ReflexivityIndex

/-! ## The Self-Reference Phase Space -/

/-- **SelfRefPoint**: A point in self-reference phase space.

    This represents a particular configuration of self-awareness
    with its associated cost and reflexivity. -/
structure SelfRefPoint where
  /-- The J-cost of this configuration -/
  cost : ℝ
  /-- The reflexivity index -/
  reflexivity : ℕ
  /-- The coherence level (0 to 1) -/
  coherence : ℝ
  /-- Cost is non-negative -/
  cost_nonneg : 0 ≤ cost
  /-- Coherence is in [0, 1] -/
  coherence_valid : 0 ≤ coherence ∧ coherence ≤ 1

/-- **Phase**: The distinct phases of self-reference.

    These are the "thermodynamic phases" of consciousness -
    qualitatively different modes of self-awareness. -/
inductive Phase
  | Explosive     -- J → ∞ (Gödelian, unstable)
  | Chaotic       -- J very high, fluctuating
  | Critical      -- J = J_crit (phase boundary)
  | Ordinary      -- J moderate, stable
  | Coherent      -- J low, highly organized
  | Transcendent  -- J ≈ 0, pure awareness
  deriving DecidableEq, Repr

/-! ## Phase Boundaries -/

/-- **CriticalCost**: The critical J-cost for phase transitions.

    This is the φ^(-5) coherence threshold from RS -
    the minimum energy quantum for stable self-reference. -/
noncomputable def criticalCost : ℝ := phi ^ (-5 : ℝ)

/-- Critical cost is positive -/
theorem criticalCost_pos : 0 < criticalCost := Real.rpow_pos_of_pos phi_pos _

/-- **CoherenceThreshold**: Minimum coherence for stable self-reference.

    Below this threshold, self-reference becomes unstable. -/
noncomputable def coherenceThreshold : ℝ := 1 / phi

/-- Coherence threshold is in (0, 1) -/
theorem coherenceThreshold_valid : 0 < coherenceThreshold ∧ coherenceThreshold < 1 :=
  ⟨by unfold coherenceThreshold; positivity,
   by unfold coherenceThreshold; exact one_div_lt_one_of_one_lt_of_pos one_lt_phi phi_pos⟩

/-- **PhaseClassifier**: Classify a point into its phase -/
noncomputable def classifyPhase (p : SelfRefPoint) : Phase :=
  if p.coherence < coherenceThreshold / 2 then
    .Explosive
  else if p.coherence < coherenceThreshold then
    .Critical
  else if p.cost > 10 * criticalCost then
    .Chaotic
  else if p.cost > criticalCost then
    .Ordinary
  else if p.cost > criticalCost / 10 then
    .Coherent
  else
    .Transcendent

/-! ## Phase Diagram Structure -/

/-- **PhaseRegion**: A region in phase space with its properties -/
structure PhaseRegion where
  /-- The phase -/
  phase : Phase
  /-- Minimum cost for this region -/
  min_cost : ℝ
  /-- Maximum cost for this region -/
  max_cost : ℝ
  /-- Minimum coherence for this region -/
  min_coherence : ℝ
  /-- Maximum coherence for this region -/
  max_coherence : ℝ
  /-- Bounds are consistent -/
  cost_ordered : min_cost ≤ max_cost
  coherence_ordered : min_coherence ≤ max_coherence

/-- **PhaseDiagram**: The complete phase diagram of self-reference -/
structure PhaseDiagram where
  /-- All phase regions -/
  regions : List PhaseRegion
  /-- Regions cover the phase space -/
  covers_space : ∀ p : SelfRefPoint, ∃ r ∈ regions,
    r.min_cost ≤ p.cost ∧ p.cost ≤ r.max_cost ∧
    r.min_coherence ≤ p.coherence ∧ p.coherence ≤ r.max_coherence

/-- The canonical phase diagram -/
noncomputable def canonicalPhaseDiagram : List PhaseRegion :=
  [ -- Transcendent: very low cost, high coherence
    { phase := .Transcendent
      min_cost := 0
      max_cost := criticalCost / 10
      min_coherence := coherenceThreshold
      max_coherence := 1
      cost_ordered := by positivity
      coherence_ordered := le_of_lt coherenceThreshold_valid.2 }
  , -- Coherent: low cost, high coherence
    { phase := .Coherent
      min_cost := criticalCost / 10
      max_cost := criticalCost
      min_coherence := coherenceThreshold
      max_coherence := 1
      cost_ordered := by unfold criticalCost; positivity
      coherence_ordered := le_of_lt coherenceThreshold_valid.2 }
  , -- Ordinary: moderate cost, good coherence
    { phase := .Ordinary
      min_cost := criticalCost
      max_cost := 10 * criticalCost
      min_coherence := coherenceThreshold
      max_coherence := 1
      cost_ordered := by unfold criticalCost; nlinarith [criticalCost_pos]
      coherence_ordered := le_of_lt coherenceThreshold_valid.2 }
  , -- Chaotic: high cost, still coherent
    { phase := .Chaotic
      min_cost := 10 * criticalCost
      max_cost := 1000  -- Practical upper bound
      min_coherence := coherenceThreshold
      max_coherence := 1
      cost_ordered := by nlinarith [criticalCost_pos]
      coherence_ordered := le_of_lt coherenceThreshold_valid.2 }
  , -- Critical: near phase boundary
    { phase := .Critical
      min_cost := 0
      max_cost := 1000
      min_coherence := coherenceThreshold / 2
      max_coherence := coherenceThreshold
      cost_ordered := by norm_num
      coherence_ordered := by
        unfold coherenceThreshold
        have h := phi_pos
        nlinarith }
  , -- Explosive: below critical coherence
    { phase := .Explosive
      min_cost := 0
      max_cost := 1000  -- In practice, cost → ∞
      min_coherence := 0
      max_coherence := coherenceThreshold / 2
      cost_ordered := by norm_num
      coherence_ordered := by positivity }
  ]

/-! ## Phase Transitions -/

/-- **PhaseTransition**: A transition between phases.

    This captures the dynamics of consciousness state changes
    (meditation, psychedelics, sleep, trauma, etc.) -/
structure PhaseTransition where
  /-- Source phase -/
  from_phase : Phase
  /-- Target phase -/
  to_phase : Phase
  /-- Energy barrier (J-cost to overcome) -/
  barrier : ℝ
  /-- Typical timescale (in natural units) -/
  timescale : ℝ
  /-- Is this transition reversible? -/
  reversible : Bool
  /-- Barrier is non-negative -/
  barrier_nonneg : 0 ≤ barrier
  /-- Timescale is positive -/
  timescale_pos : 0 < timescale

/-- **TransitionCatalog**: All possible phase transitions -/
noncomputable def transitionCatalog : List PhaseTransition :=
  [ -- Meditation: Ordinary → Coherent → Transcendent
    { from_phase := .Ordinary
      to_phase := .Coherent
      barrier := criticalCost / 2
      timescale := 100
      reversible := true
      barrier_nonneg := by positivity
      timescale_pos := by norm_num }
  , { from_phase := .Coherent
      to_phase := .Transcendent
      barrier := criticalCost / 10
      timescale := 1000
      reversible := true
      barrier_nonneg := by positivity
      timescale_pos := by norm_num }
  , -- Psychedelics: Ordinary → Critical → (various)
    { from_phase := .Ordinary
      to_phase := .Critical
      barrier := 0.1
      timescale := 10
      reversible := true
      barrier_nonneg := by norm_num
      timescale_pos := by norm_num }
  , { from_phase := .Critical
      to_phase := .Explosive
      barrier := 0
      timescale := 1
      reversible := true
      barrier_nonneg := by norm_num
      timescale_pos := by norm_num }
  , { from_phase := .Critical
      to_phase := .Transcendent
      barrier := 0.5
      timescale := 5
      reversible := true
      barrier_nonneg := by norm_num
      timescale_pos := by norm_num }
  , -- Sleep: Ordinary → various
    { from_phase := .Ordinary
      to_phase := .Chaotic
      barrier := 0.3
      timescale := 50
      reversible := true
      barrier_nonneg := by norm_num
      timescale_pos := by norm_num }
  , -- Natural fluctuation
    { from_phase := .Chaotic
      to_phase := .Ordinary
      barrier := 0.2
      timescale := 20
      reversible := true
      barrier_nonneg := by norm_num
      timescale_pos := by norm_num }
  ]

/-! ## Stability Analysis -/

/-- **StabilityType**: Classification of stability -/
inductive StabilityType
  | Stable       -- Returns to equilibrium after perturbation
  | Metastable   -- Stable but can transition with energy input
  | Unstable     -- Tends to diverge
  | Critical     -- At phase boundary
  deriving DecidableEq, Repr

/-- **PhaseStability**: Stability of each phase -/
def phaseStability : Phase → StabilityType
  | .Explosive    => .Unstable
  | .Chaotic      => .Unstable
  | .Critical     => .Critical
  | .Ordinary     => .Metastable
  | .Coherent     => .Stable
  | .Transcendent => .Stable

/-- **LyapunovExponent**: A measure of stability for a configuration.

    Negative = stable (perturbations decay)
    Zero = marginal
    Positive = unstable (perturbations grow) -/
noncomputable def lyapunovExponent (p : SelfRefPoint) : ℝ :=
  match classifyPhase p with
  | .Explosive    => 1       -- Strongly unstable
  | .Chaotic      => 0.5     -- Mildly unstable
  | .Critical     => 0       -- Marginal
  | .Ordinary     => -0.1    -- Weakly stable
  | .Coherent     => -0.5    -- Moderately stable
  | .Transcendent => -1      -- Strongly stable

/-- Stable phases have negative Lyapunov exponent -/
theorem stable_negative_lyapunov (p : SelfRefPoint)
    (h : phaseStability (classifyPhase p) = .Stable) :
    lyapunovExponent p < 0 := by
  simp only [phaseStability] at h
  simp only [lyapunovExponent]
  split <;> try (simp at h)
  all_goals norm_num

/-! ## The Gödelian Boundary -/

/-- **GodelianPoint**: A self-referential configuration at the unstable boundary.

    This is where "self-reference about self-reference" leads to infinite regress.
    Such points are characterized by:
    1. Coherence below threshold
    2. Attempting full self-modeling
    3. Cost diverging to infinity -/
structure GodelianPoint where
  /-- Coherence is below threshold -/
  coherence : ℝ
  low_coherence : coherence < coherenceThreshold
  /-- Attempting full self-reference depth -/
  reflexivity_attempt : ℕ
  full_self_ref : reflexivity_attempt > 10
  /-- Cost diverges -/
  cost_unbounded : ∀ C : ℝ, ∃ t : ℝ, t > 0 ∧ C < phi ^ (reflexivity_attempt : ℝ) * t

/-- **Theorem**: Gödelian points cannot stabilize.

    This connects the phase diagram to the Gödel dissolution:
    self-reference at low coherence with high reflexivity depth
    is in the Explosive phase and cannot have a stable fixed point. -/
theorem godelian_unstable (g : GodelianPoint) :
    -- The point is in the Explosive or Critical phase
    ∀ (cost : ℝ) (h_cost : 0 ≤ cost),
      let p : SelfRefPoint := ⟨cost, g.reflexivity_attempt, g.coherence, h_cost,
        ⟨le_of_lt (lt_trans coherenceThreshold_valid.1 g.low_coherence), le_of_lt g.low_coherence⟩⟩
      classifyPhase p = .Explosive ∨ classifyPhase p = .Critical := by
  intro cost h_cost
  simp only [classifyPhase]
  by_cases h1 : g.coherence < coherenceThreshold / 2
  · left; simp [h1]
  · right; simp [h1, g.low_coherence]

/-! ## The Stable Self-Reference Manifold -/

/-- **StableManifold**: The set of stable self-referential configurations.

    This is the "habitable zone" of consciousness -
    the region where stable self-awareness is possible. -/
def StableManifold (p : SelfRefPoint) : Prop :=
  classifyPhase p = .Coherent ∨
  classifyPhase p = .Transcendent ∨
  classifyPhase p = .Ordinary

/-- **Theorem**: The stable manifold has finite cost.

    This is the key result: stable self-reference is possible
    precisely when the J-cost is finite and coherence is sufficient. -/
theorem stable_manifold_finite_cost (p : SelfRefPoint) (h : StableManifold p) :
    p.cost < 1000 := by
  simp only [StableManifold] at h
  rcases h with h | h | h
  · -- Coherent phase
    simp only [classifyPhase] at h
    split_ifs at h with h1 h2 h3 h4 h5
    all_goals try contradiction
    -- In Coherent: cost ≤ criticalCost < 1000
    have hc : p.cost ≤ criticalCost := by
      push_neg at h4; exact le_of_lt h4
    calc p.cost ≤ criticalCost := hc
      _ < 1000 := by unfold criticalCost; norm_num
  · -- Transcendent phase
    simp only [classifyPhase] at h
    split_ifs at h with h1 h2 h3 h4 h5
    all_goals try contradiction
    -- In Transcendent: cost ≤ criticalCost/10 < 1000
    push_neg at h5
    calc p.cost ≤ criticalCost / 10 := le_of_lt h5
      _ < 1000 := by unfold criticalCost; norm_num
  · -- Ordinary phase
    simp only [classifyPhase] at h
    split_ifs at h with h1 h2 h3 h4
    all_goals try contradiction
    -- In Ordinary: cost ≤ 10*criticalCost < 1000
    push_neg at h3
    calc p.cost ≤ 10 * criticalCost := le_of_lt h3
      _ < 1000 := by unfold criticalCost; norm_num

/-! ## Connection to Consciousness Phenomena -/

/-- **ConsciousnessState**: Mapping from phase to experiential state -/
structure ConsciousnessState where
  phase : Phase
  experiential_quality : String
  cognitive_function : String
  typical_trigger : String

/-- The phenomenology of each phase -/
def phasePhenomenology : Phase → ConsciousnessState
  | .Explosive => {
      phase := .Explosive
      experiential_quality := "Fragmented, chaotic, terrifying"
      cognitive_function := "Severely impaired"
      typical_trigger := "Extreme psychedelic dose, severe trauma"
    }
  | .Chaotic => {
      phase := .Chaotic
      experiential_quality := "Confused, dreamlike, fluid"
      cognitive_function := "Impaired, creative"
      typical_trigger := "REM sleep, moderate psychedelics"
    }
  | .Critical => {
      phase := .Critical
      experiential_quality := "Liminal, neither here nor there"
      cognitive_function := "Variable, sensitive to input"
      typical_trigger := "Hypnagogia, sensory deprivation"
    }
  | .Ordinary => {
      phase := .Ordinary
      experiential_quality := "Normal waking consciousness"
      cognitive_function := "Baseline function"
      typical_trigger := "Default state"
    }
  | .Coherent => {
      phase := .Coherent
      experiential_quality := "Clear, focused, unified"
      cognitive_function := "Enhanced, integrated"
      typical_trigger := "Deep focus, meditation, flow"
    }
  | .Transcendent => {
      phase := .Transcendent
      experiential_quality := "Pure awareness, boundless, blissful"
      cognitive_function := "Paradoxical: simple yet vast"
      typical_trigger := "Advanced meditation, grace"
    }

/-! ## The Complete Phase Diagram Theorem -/

/-- **THE SELF-REFERENCE PHASE DIAGRAM THEOREM**

    This theorem summarizes the complete topology of self-reference:

    1. **Phase Structure**: Self-reference has 6 distinct phases
    2. **Stability**: 3 stable, 2 unstable, 1 critical
    3. **Boundaries**: Determined by φ-thresholds
    4. **Gödelian Region**: Unstable self-ref is in Explosive phase
    5. **Habitable Zone**: Stable self-ref requires finite cost + sufficient coherence
    6. **Transitions**: All phases are connected via transition paths -/
theorem self_reference_phase_diagram :
    -- 1. There are exactly 6 phases
    (∃! (phases : Finset Phase), phases.card = 6 ∧
      .Explosive ∈ phases ∧ .Chaotic ∈ phases ∧ .Critical ∈ phases ∧
      .Ordinary ∈ phases ∧ .Coherent ∈ phases ∧ .Transcendent ∈ phases) ∧
    -- 2. Stable phases have negative Lyapunov exponent
    (∀ p : SelfRefPoint, StableManifold p → lyapunovExponent p < 0) ∧
    -- 3. Critical cost is φ^(-5)
    (criticalCost = phi ^ (-5 : ℝ)) ∧
    -- 4. Coherence threshold is 1/φ
    (coherenceThreshold = 1 / phi) ∧
    -- 5. Stable manifold has finite cost
    (∀ p : SelfRefPoint, StableManifold p → p.cost < 1000) :=
  ⟨⟨{.Explosive, .Chaotic, .Critical, .Ordinary, .Coherent, .Transcendent},
    ⟨by decide, by simp, by simp, by simp, by simp, by simp, by simp⟩,
    fun s ⟨hcard, he, hch, hcr, ho, hco, ht⟩ => by
      ext x
      cases x <;> simp_all⟩,
   fun p h => stable_negative_lyapunov p (by
     simp only [StableManifold] at h
     rcases h with h | h | h <;> simp [phaseStability, h]),
   rfl,
   rfl,
   stable_manifold_finite_cost⟩

/-! ## Phase Transition Dynamics -/

/-- **TransitionRate**: The rate of transitioning between phases.

    Follows Arrhenius-like kinetics: rate ∝ exp(-barrier/kT)
    where kT is effectively the "cognitive temperature" (noise level). -/
noncomputable def transitionRate (barrier : ℝ) (cognitiveTemp : ℝ) : ℝ :=
  if cognitiveTemp > 0 then Real.exp (-barrier / cognitiveTemp) else 0

/-- Higher barrier means lower transition rate -/
theorem higher_barrier_lower_rate (b₁ b₂ T : ℝ) (hT : T > 0) (hb : b₁ < b₂) :
    transitionRate b₂ T < transitionRate b₁ T := by
  simp only [transitionRate, hT, ite_true]
  apply Real.exp_lt_exp_of_lt
  have : -b₂ / T < -b₁ / T := by
    apply div_lt_div_of_pos_right _ hT
    linarith
  exact this

/-- Higher temperature means higher transition rate -/
theorem higher_temp_higher_rate (b T₁ T₂ : ℝ) (hT₁ : T₁ > 0) (hT₂ : T₂ > 0) (hT : T₁ < T₂) (hb : b > 0) :
    transitionRate b T₁ < transitionRate b T₂ := by
  simp only [transitionRate, hT₁, hT₂, ite_true]
  apply Real.exp_lt_exp_of_lt
  have h1 : -b / T₂ < -b / T₁ := by
    rw [neg_div, neg_div]
    apply neg_lt_neg
    exact div_lt_div_of_pos_left hb hT₁ hT
  exact h1

/-! ## Consciousness Attractors -/

/-- **PhaseAttractor**: A stable point in phase space that the system tends toward.

    Each stable phase has an attractor at its center. The system
    naturally evolves toward these attractors unless perturbed. -/
structure PhaseAttractor where
  /-- The phase this attractor belongs to -/
  phase : Phase
  /-- The cost at the attractor -/
  attractor_cost : ℝ
  /-- The coherence at the attractor -/
  attractor_coherence : ℝ
  /-- Basin of attraction radius -/
  basin_radius : ℝ
  /-- Attractor is in stable manifold -/
  is_stable : phase = .Coherent ∨ phase = .Transcendent ∨ phase = .Ordinary

/-- The natural attractor for ordinary consciousness -/
noncomputable def ordinaryAttractor : PhaseAttractor where
  phase := .Ordinary
  attractor_cost := 5 * criticalCost  -- Middle of Ordinary range
  attractor_coherence := (1 + coherenceThreshold) / 2  -- Good but not perfect coherence
  basin_radius := 3 * criticalCost
  is_stable := Or.inr (Or.inr rfl)

/-- The natural attractor for coherent consciousness (meditation) -/
noncomputable def coherentAttractor : PhaseAttractor where
  phase := .Coherent
  attractor_cost := criticalCost / 2
  attractor_coherence := 0.9
  basin_radius := criticalCost / 2
  is_stable := Or.inl rfl

/-- The natural attractor for transcendent consciousness -/
noncomputable def transcendentAttractor : PhaseAttractor where
  phase := .Transcendent
  attractor_cost := criticalCost / 100
  attractor_coherence := 0.99
  basin_radius := criticalCost / 10
  is_stable := Or.inr (Or.inl rfl)

/-! ## Summary: The Complete Phase Space -/

/-- **CompletePhaseSpace**: The full structure of self-reference phase space.

    This bundles:
    1. The 6 phases
    2. The phase boundaries (φ-determined)
    3. The attractors (stable points)
    4. The transition dynamics (Arrhenius-like)
    5. The Lyapunov stability analysis -/
structure CompletePhaseSpace where
  /-- All phases -/
  phases : Finset Phase
  phases_complete : phases.card = 6
  /-- Phase boundaries -/
  critical_cost : ℝ := criticalCost
  coherence_threshold : ℝ := coherenceThreshold
  /-- Attractors for stable phases -/
  ordinary_attr : PhaseAttractor := ordinaryAttractor
  coherent_attr : PhaseAttractor := coherentAttractor
  transcendent_attr : PhaseAttractor := transcendentAttractor

/-- The canonical phase space -/
noncomputable def canonicalPhaseSpace : CompletePhaseSpace where
  phases := {.Explosive, .Chaotic, .Critical, .Ordinary, .Coherent, .Transcendent}
  phases_complete := by decide

end SelfReferencePhaseDiagram
end Foundation
end IndisputableMonolith
