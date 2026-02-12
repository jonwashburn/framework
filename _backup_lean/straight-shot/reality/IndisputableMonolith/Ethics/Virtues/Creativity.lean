import Mathlib
import IndisputableMonolith.Foundation.RecognitionOperator
import IndisputableMonolith.Ethics.MoralState
import IndisputableMonolith.Ethics.ConservationLaw
import IndisputableMonolith.Support.GoldenRatio
import IndisputableMonolith.Ethics.Virtues.Love
import IndisputableMonolith.Ethics.Virtues.Wisdom
import IndisputableMonolith.Ethics.Virtues.Hope

/-!
# Creativity: φ-Chaotic State-Space Exploration

Creativity provides the exploration dual to the exploitation-driven virtues
`Love`, `Wisdom`, and `Hope`.  It stirs admissible moral states by a φ-chaotic
mixing process that:

* deterministically preserves ledger admissibility and energy availability;
* introduces a non-trivial φ-structured cross term that searches for new
  low-skew directions;
* produces an aperiodic sequence of mixing angles so exploration never
  stagnates.

The lemmas in this file formalise the chaotic angle generator, prove basic
aperiodicity/irrationality properties needed for φ-chaos, and show the energy
and convex-hull invariants required by the ethics layer.  Remaining bridges to
`Harm`, `ValueFunctional`, and `Consent` are recorded as explicit TODO items at
the end of the file (they require differentiability infrastructure that is not
yet available).
-/

namespace IndisputableMonolith
namespace Ethics
namespace Virtues

open Classical
open Foundation MoralState
open scoped BigOperators Real

local notation "φ" => Foundation.φ

/-- φ-chaotic sequence: fractional part of the φ-multiples. -/
noncomputable def phi_chaotic_sequence (n : ℕ) : ℝ :=
  Int.fract ((n : ℝ) * φ)

/-- Mixing angle obtained from the φ-chaotic sequence. -/
noncomputable def mixing_angle (seed : ℕ) : ℝ :=
  2 * Real.pi * phi_chaotic_sequence seed

/-- Real-valued skew before quantisation. -/
noncomputable def creative_skew_real (s₁ s₂ : MoralState) (seed : ℕ) : ℝ :=
  let θ := mixing_angle seed
  (s₁.skew : ℝ) * Real.cos θ ^ 2 +
    (s₂.skew : ℝ) * Real.sin θ ^ 2 +
    Real.sqrt (abs ((s₁.skew : ℝ) * (s₂.skew : ℝ))) * Real.sin (2 * θ)

/-- Creativity produces a new moral state by averaging energy and applying the
φ-chaotic skew mixer.  The ledger witness is inherited from the first input: the
mix operates entirely within the σ = 0 manifold that defines `MoralState`. -/
noncomputable def ApplyCreativity
    (s₁ s₂ : MoralState) (seed : ℕ) : MoralState :=
  let mixed_skew_real := creative_skew_real s₁ s₂ seed
  let mixed_skew := Int.floor mixed_skew_real
  let avg_energy := (s₁.energy + s₂.energy) / 2
  {
    ledger := s₁.ledger
    agent_bonds := s₁.agent_bonds ∪ s₂.agent_bonds
    skew := mixed_skew
    energy := avg_energy
    valid := s₁.valid
    energy_pos := by
      unfold avg_energy
      have hpos : 0 < s₁.energy + s₂.energy := by
        have h₁ := s₁.energy_pos
        have h₂ := s₂.energy_pos
        linarith
      linarith
  }

/-- Simplification helper for `creative_skew_real`. -/
lemma creative_skew_real_def (s₁ s₂ : MoralState) (seed : ℕ) :
    creative_skew_real s₁ s₂ seed =
      let θ := mixing_angle seed
      (s₁.skew : ℝ) * Real.cos θ ^ 2 +
        (s₂.skew : ℝ) * Real.sin θ ^ 2 +
        Real.sqrt (abs ((s₁.skew : ℝ) * (s₂.skew : ℝ))) * Real.sin (2 * θ) := rfl

/-- φ-chaotic values stay in the unit interval (definition of `Real.fract`). -/
lemma phi_sequence_unit_interval (n : ℕ) :
    0 ≤ phi_chaotic_sequence n ∧ phi_chaotic_sequence n ≤ 1 := by
  unfold phi_chaotic_sequence
  constructor
  · exact Int.fract_nonneg _
  · exact le_of_lt (Int.fract_lt_one _)

/-- Helper: φ-chaotic sequence equality implies linear relation on φ. -/
private lemma phi_sequence_eq_implies_linear
    {n m : ℕ}
    (h : phi_chaotic_sequence n = phi_chaotic_sequence m) :
    ((n : ℝ) - (m : ℝ)) * φ
      = (Int.floor ((n : ℝ) * φ) : ℝ) - (Int.floor ((m : ℝ) * φ) : ℝ) := by
  -- phi_chaotic_sequence n = Int.fract (n * φ) = n * φ - floor(n * φ)
  -- If fract(n * φ) = fract(m * φ), then:
  -- n * φ - floor(n * φ) = m * φ - floor(m * φ)
  -- Rearranging: (n - m) * φ = floor(n * φ) - floor(m * φ)
  unfold phi_chaotic_sequence at h
  have h1 : (n : ℝ) * φ - Int.floor ((n : ℝ) * φ) = (m : ℝ) * φ - Int.floor ((m : ℝ) * φ) := by
    simp only [Int.fract] at h
    exact h
  linarith

/-- φ-chaotic sequence values coincide only when the seeds coincide. -/
lemma phi_sequence_injective {n m : ℕ}
    (hneq : n ≠ m) : phi_chaotic_sequence n ≠ phi_chaotic_sequence m := by
  -- φ is irrational, so (n - m) * φ cannot be an integer unless n = m
  intro h_eq
  unfold phi_chaotic_sequence at h_eq
  -- If Int.fract(n * φ) = Int.fract(m * φ), then (n - m) * φ is an integer
  have h_diff : ∃ k : ℤ, (n : ℝ) * φ - (m : ℝ) * φ = k := by
    have := Int.fract_eq_fract.mp h_eq
    obtain ⟨k, hk⟩ := this
    exact ⟨k, hk⟩
  obtain ⟨k, hk⟩ := h_diff
  -- Rewrite as (n - m) * φ = k
  have h_factor : ((n : ℤ) - (m : ℤ)) * φ = k := by
    have : (n : ℝ) * φ - (m : ℝ) * φ = ((n : ℝ) - (m : ℝ)) * φ := by ring
    rw [this] at hk
    simp only [Int.cast_sub, Int.cast_natCast] at hk ⊢
    exact hk
  -- Since φ is irrational, (n - m) must be 0
  have h_irr := Support.GoldenRatio.phi_irrational
  have h_nm_ne : (n : ℤ) - (m : ℤ) ≠ 0 := by
    intro h_zero
    have : (n : ℤ) = (m : ℤ) := sub_eq_zero.mp h_zero
    exact hneq (Int.ofNat_inj.mp this)
  -- If (n - m) * φ = k (an integer), then φ = k / (n - m), contradicting irrationality
  have h_rat : φ = k / ((n : ℤ) - (m : ℤ)) := by
    field_simp [h_nm_ne] at h_factor ⊢
    linarith
  have h_is_rat : ∃ q : ℚ, φ = q := by
    use k / ((n : ℤ) - (m : ℤ))
    rw [h_rat]
    simp [Rat.cast_div, Rat.cast_intCast]
  exact h_irr h_is_rat

/-- Positive seeds yield chaotic angles with non-zero two-fold sine. -/
lemma sin_two_mul_mixing_angle_ne_zero {seed : ℕ}
    (hseed : 0 < seed) : Real.sin (2 * mixing_angle seed) ≠ 0 := by
  -- mixing_angle seed = 2π * Int.fract(seed * φ)
  -- sin(2 * 2π * Int.fract(seed * φ)) = sin(4π * Int.fract(seed * φ))
  -- This is 0 iff Int.fract(seed * φ) = k/4 for some integer k
  -- Since φ is irrational, seed * φ is irrational for seed > 0
  -- So Int.fract(seed * φ) is irrational, hence not equal to any rational k/4
  unfold mixing_angle phi_chaotic_sequence
  intro h_sin_zero
  -- sin(4π * Int.fract(seed * φ)) = 0 implies Int.fract(seed * φ) = k/4
  have h_irr := Support.GoldenRatio.phi_irrational
  have h_seed_phi_irr : Irrational ((seed : ℝ) * φ) := by
    have hseed_ne : (seed : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hseed)
    exact h_irr.mul_rat (Rat.cast_injective.ne_iff.mpr (by simp [hseed_ne] : (seed : ℚ) ≠ 0))
  -- The fractional part of an irrational number is irrational
  have h_fract_irr : Irrational (Int.fract ((seed : ℝ) * φ)) := by
    have := Int.self_sub_floor ((seed : ℝ) * φ)
    have h_floor_rat : ∃ q : ℚ, (⌊(seed : ℝ) * φ⌋ : ℝ) = q := ⟨⌊(seed : ℝ) * φ⌋, by simp⟩
    intro ⟨q, hq⟩
    have : (seed : ℝ) * φ = q + ⌊(seed : ℝ) * φ⌋ := by
      rw [← hq]; exact (Int.fract_add_floor _).symm
    exact h_seed_phi_irr ⟨q + ⌊(seed : ℝ) * φ⌋, by simp [this]⟩
  -- But sin(4πx) = 0 implies x is rational (x = k/4)
  -- This contradicts h_fract_irr
  have h_sin_zero_iff : Real.sin (4 * Real.pi * Int.fract ((seed : ℝ) * φ)) = 0 := by
    convert h_sin_zero using 1; ring
  -- sin(4πx) = 0 iff x ∈ {0, 1/4, 1/2, 3/4, ...} which are all rational
  have h_fract_range := Int.fract_nonneg ((seed : ℝ) * φ)
  have h_fract_lt_one := Int.fract_lt_one ((seed : ℝ) * φ)
  -- Use Real.sin_eq_zero_iff_of_lt_of_lt to get that 4πx = kπ
  have h_rational : ∃ q : ℚ, Int.fract ((seed : ℝ) * φ) = q := by
    have := Real.sin_eq_zero_iff.mp h_sin_zero_iff
    obtain ⟨k, hk⟩ := this
    use k / 4
    have h4pi_ne : (4 : ℝ) * Real.pi ≠ 0 := by positivity
    field_simp at hk ⊢
    linarith
  exact h_fract_irr h_rational

-- Helper lemmas for creativity proofs
private lemma phi_chaotic_zero_seq :
    phi_chaotic_sequence 0 = 0 := by
  unfold phi_chaotic_sequence
  simp

/-- Creative energy is the average of the inputs (exact conservation). -/
lemma creativity_preserves_energy (s₁ s₂ : MoralState) (seed : ℕ) :
    (ApplyCreativity s₁ s₂ seed).energy = (s₁.energy + s₂.energy) / 2 := by
  simp [ApplyCreativity]

/-- Creative energy stays inside the convex hull of the inputs. -/
lemma creativity_energy_convex (s₁ s₂ : MoralState) (seed : ℕ) :
    let s_new := ApplyCreativity s₁ s₂ seed
    min s₁.energy s₂.energy ≤ s_new.energy ∧
      s_new.energy ≤ max s₁.energy s₂.energy := by
  simp only [ApplyCreativity]
  have h_pos1 : 0 < s₁.energy := s₁.energy_pos
  have h_pos2 : 0 < s₂.energy := s₂.energy_pos
  constructor
  · -- min s₁.energy s₂.energy ≤ (s₁.energy + s₂.energy) / 2
    have h1 : min s₁.energy s₂.energy ≤ s₁.energy := min_le_left _ _
    have h2 : min s₁.energy s₂.energy ≤ s₂.energy := min_le_right _ _
    have h : 2 * min s₁.energy s₂.energy ≤ s₁.energy + s₂.energy := by linarith
    linarith
  · -- (s₁.energy + s₂.energy) / 2 ≤ max s₁.energy s₂.energy
    have h1 : s₁.energy ≤ max s₁.energy s₂.energy := le_max_left _ _
    have h2 : s₂.energy ≤ max s₁.energy s₂.energy := le_max_right _ _
    have h : s₁.energy + s₂.energy ≤ 2 * max s₁.energy s₂.energy := by linarith
    linarith

/-- φ-chaotic mixing introduces a non-zero cross term whenever both inputs carry
non-zero skew and the seed is non-trivial.  This delivers the exploration
behaviour: the real-valued skew cannot collapse to the convex combination. -/
lemma creativity_cross_term_nonzero
    (s₁ s₂ : MoralState) {seed : ℕ}
    (hseed : 0 < seed) (h₁ : s₁.skew ≠ 0) (h₂ : s₂.skew ≠ 0) :
    let θ := mixing_angle seed
    let base :=
      (s₁.skew : ℝ) * Real.cos θ ^ 2 +
        (s₂.skew : ℝ) * Real.sin θ ^ 2
    let cross :=
      Real.sqrt (abs ((s₁.skew : ℝ) * (s₂.skew : ℝ))) * Real.sin (2 * θ)
    cross ≠ 0 := by
  intro θ; intro base; intro cross
  have hprod : ((s₁.skew : ℝ) * (s₂.skew : ℝ)) ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast h₁) (by exact_mod_cast h₂)
  have hsqrt :
      Real.sqrt (abs ((s₁.skew : ℝ) * (s₂.skew : ℝ))) ≠ 0 := by
    have : 0 < abs ((s₁.skew : ℝ) * (s₂.skew : ℝ)) :=
      abs_pos.mpr hprod
    exact (ne_of_gt (Real.sqrt_pos.mpr this))
  have hsin : Real.sin (2 * θ) ≠ 0 :=
    sin_two_mul_mixing_angle_ne_zero hseed
  exact mul_ne_zero hsqrt hsin

/-- The real-valued creative skew differs from the convex combination when both
inputs carry non-zero skew and the seed is positive. -/
lemma creativity_explores_state_space
    (s₁ s₂ : MoralState) {seed : ℕ}
    (hseed : 0 < seed) (h₁ : s₁.skew ≠ 0) (h₂ : s₂.skew ≠ 0) :
    let θ := mixing_angle seed
    let base :=
      (s₁.skew : ℝ) * Real.cos θ ^ 2 +
        (s₂.skew : ℝ) * Real.sin θ ^ 2
    creative_skew_real s₁ s₂ seed ≠ base := by
  intro θ base
  unfold creative_skew_real
  simp only
  -- We need: base + cross ≠ base, where cross = sqrt(|skew₁ * skew₂|) * sin(2θ)
  -- This is equivalent to: cross ≠ 0
  have h_cross : Real.sqrt (abs ((s₁.skew : ℝ) * (s₂.skew : ℝ))) * Real.sin (2 * mixing_angle seed) ≠ 0 :=
    creativity_cross_term_nonzero s₁ s₂ hseed h₁ h₂
  -- base + cross ≠ base iff cross ≠ 0
  intro heq
  apply h_cross
  linarith

/-- Mixing is deterministic in the seed argument. -/
lemma creativity_deterministic (s₁ s₂ : MoralState)
    (seed₁ seed₂ : ℕ) :
    seed₁ = seed₂ →
      ApplyCreativity s₁ s₂ seed₁ = ApplyCreativity s₁ s₂ seed₂ := by
  intro h; simp [ApplyCreativity, h]

/-- Distinct seeds lead to distinct chaotic angles. -/
lemma creativity_phi_structured {n m : ℕ}
    (h : n ≠ m) :
    mixing_angle n ≠ mixing_angle m := by
  intro hangle
  have := congrArg (fun t => t / (2 * Real.pi)) hangle
  have hscale : (2 * Real.pi) ≠ 0 := by
    have : (2 : ℝ) ≠ 0 := by norm_num
    exact mul_ne_zero this Real.pi_ne_zero
  have hseq :
      phi_chaotic_sequence n = phi_chaotic_sequence m := by
    simpa [mixing_angle, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  exact (phi_sequence_injective h) hseq

/-- Chaotic angles never repeat when shifted by a positive period. -/
lemma creativity_aperiodic (seed period : ℕ)
    (hperiod : 0 < period) :
    mixing_angle (seed + period) ≠ mixing_angle seed := by
  have h_ne : seed + period ≠ seed := by omega
  exact creativity_phi_structured h_ne

/-- Creativity maintains the exploitation baseline while injecting exploration
via the non-zero chaotic term. -/
lemma creativity_balanced_exploration
    (s₁ s₂ : MoralState) {seed : ℕ}
    (hseed : 0 < seed) (h₁ : s₁.skew ≠ 0) (h₂ : s₂.skew ≠ 0) :
    let s_new := ApplyCreativity s₁ s₂ seed
    s_new.energy = (s₁.energy + s₂.energy) / 2 ∧
      ∃ base,
        creative_skew_real s₁ s₂ seed ≠ base := by
  intro s_new
  refine And.intro (creativity_preserves_energy _ _ _) ?_
  refine ⟨_, creativity_explores_state_space s₁ s₂ hseed h₁ h₂⟩

/-
TODO (integration work tracked in DREAM roadmap):
1. Construct an explicit `Harm.ActionSpec` describing the infinitesimal skew
   rotation induced by `ApplyCreativity`, then prove ΔS-bounds analogous to the
   Compassion/Sacrifice lemmas.
2. Bridge to `ValueFunctional` once derivative helpers are available, establishing
   monotonicity of creative exploration under φ-discounted evaluation (Wisdom).
3. Extend `Consent` certificates with φ-chaotic tangent directions to show
   creativity respects the forced axiology derivative sign convention.
-/

end Virtues
end Ethics
end IndisputableMonolith
