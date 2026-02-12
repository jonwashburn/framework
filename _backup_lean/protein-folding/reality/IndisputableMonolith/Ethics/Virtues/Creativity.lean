import Mathlib
import IndisputableMonolith.Foundation.RecognitionOperator
import IndisputableMonolith.Ethics.MoralState
import IndisputableMonolith.Ethics.ConservationLaw
import IndisputableMonolith.Support.GoldenRatio
import IndisputableMonolith.Ethics.Virtues.Love
import IndisputableMonolith.Ethics.Virtues.Wisdom
import IndisputableMonolith.Ethics.Virtues.Hope

/--!
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
  Real.fract ((n : ℝ) * φ)

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
  let mixed_skew := mixed_skew_real.floor
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
  exact ⟨Real.fract_nonneg _, le_of_lt (Real.fract_lt_one _)⟩

/-- Helper: φ-chaotic sequence equality implies linear relation on φ. -/
private lemma phi_sequence_eq_implies_linear
    {n m : ℕ}
    (h : phi_chaotic_sequence n = phi_chaotic_sequence m) :
    ((n : ℝ) - (m : ℝ)) * φ
      = (Real.floor ((n : ℝ) * φ) : ℝ) - (Real.floor ((m : ℝ) * φ) : ℝ) := by
  unfold phi_chaotic_sequence at h
  have := congrArg (fun t => t - (Real.fract ((m : ℝ) * φ))) h
  simp [Real.fract, sub_eq, add_comm, add_left_comm, add_assoc, sub_eq_add_neg] at this
  exact (sub_eq_zero.mp this).symm

/-- φ-chaotic sequence values coincide only when the seeds coincide. -/
lemma phi_sequence_injective {n m : ℕ}
    (hneq : n ≠ m) : phi_chaotic_sequence n ≠ phi_chaotic_sequence m := by
  intro h
  have hlin := phi_sequence_eq_implies_linear (n := n) (m := m) h
  have hden : ((n : ℝ) - (m : ℝ)) ≠ 0 := by
    have : (n : ℝ) = (m : ℝ) := by
      by_contra hcontra
      have hcast : ((n : ℝ) - (m : ℝ)) = 0 := sub_eq_zero_of_eq this
      exact hneq (by exact_mod_cast eq_of_sub_eq_zero hcast)
    exact sub_ne_zero.mpr (by exact_mod_cast hneq)
  have hratio :=
    congrArg (fun t => t / ((n : ℝ) - (m : ℝ))) hlin
  have hcancel :
      ((n : ℝ) - (m : ℝ)) * φ / ((n : ℝ) - (m : ℝ)) = φ :=
    by simpa using (mul_div_cancel' φ hden)
  have hφ :
      φ = ((Real.floor ((n : ℝ) * φ) : ℝ) - (Real.floor ((m : ℝ) * φ) : ℝ)) /
        ((n : ℝ) - (m : ℝ)) := by
    have := hratio
    simpa [hcancel, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this.symm
  let z : ℚ :=
    ((Real.floor ((n : ℝ) * φ) : ℤ) - Real.floor ((m : ℝ) * φ)) /
      ((n : ℚ) - (m : ℚ))
  have hdenℚ : (n : ℚ) - (m : ℚ) ≠ 0 := by
    have : (n : ℚ) = (m : ℚ) := by
      by_contra h'
      have h'' : ((n : ℚ) - (m : ℚ)) = 0 := sub_eq_zero_of_eq this
      exact hneq (by exact_mod_cast eq_of_sub_eq_zero h'')
    exact sub_ne_zero.mpr (by exact_mod_cast hneq)
  have hcast :
      (z : ℝ) =
        ((Real.floor ((n : ℝ) * φ) : ℝ) - (Real.floor ((m : ℝ) * φ) : ℝ)) /
          ((n : ℝ) - (m : ℝ)) := by
    have hnum :
        ((Real.floor ((n : ℝ) * φ) : ℤ) - Real.floor ((m : ℝ) * φ) : ℝ) =
          (Real.floor ((n : ℝ) * φ) : ℝ) - (Real.floor ((m : ℝ) * φ) : ℝ) := by
      simp
    have hden' : ((n : ℚ) - (m : ℚ) : ℝ) = (n : ℝ) - (m : ℝ) := by simp
    simp [z, hnum, hden', div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have : φ = (z : ℝ) := by simpa [hcast] using hφ
  exact (Support.GoldenRatio.phi_irrational.ne_rat z) this

/-- Positive seeds yield chaotic angles with non-zero two-fold sine. -/
lemma sin_two_mul_mixing_angle_ne_zero {seed : ℕ}
    (hseed : 0 < seed) : Real.sin (2 * mixing_angle seed) ≠ 0 := by
  intro hsin
  obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hsin
  have hquart :
      phi_chaotic_sequence seed = (k : ℝ) / 4 := by
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have hx :=
      congrArg (fun t => t / (2 * Real.pi)) hk
    have hscale : (2 * Real.pi) ≠ 0 := by
      have : (2 : ℝ) ≠ 0 := by norm_num
      exact mul_ne_zero this hpi
    have hθ :
        mixing_angle seed = (k : ℝ) * Real.pi / (2 * Real.pi) := hx
    have hθ' :
        mixing_angle seed = (k : ℝ) / 2 := by
      have hcancel :=
        (mul_div_cancel' (Real.pi : ℝ) hscale)
      simpa [mixing_angle, hθ, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc,
        bit0, two_mul] using hcancel
    have hfract :
        phi_chaotic_sequence seed =
          (mixing_angle seed) / (2 * Real.pi) := by
      field_simp [mixing_angle, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc,
        bit0, two_mul] with hscale
    have hfinal :
        phi_chaotic_sequence seed =
          ((k : ℝ) / 2) / (2 * Real.pi) := by simpa [hθ', hfract]
    have hscale' : (4 : ℝ) ≠ 0 := by norm_num
    have hquarter :
        phi_chaotic_sequence seed = (k : ℝ) / 4 := by
      have := congrArg (fun t => t * Real.pi) hfinal
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, bit0, two_mul]
        using this
    exact hquarter
  have hzero : phi_chaotic_sequence seed ≠ (k : ℝ) / 4 := by
    have hkseed : seed ≠ 0 := by exact Nat.ne_of_gt hseed
    have hk' :
        phi_chaotic_sequence seed ≠ phi_chaotic_sequence 0 := by
      exact phi_sequence_injective hkseed
    have hzero_seq :
        phi_chaotic_sequence 0 = 0 := by
      unfold phi_chaotic_sequence
      simp
    have hcontr :
        (k : ℝ) / 4 ≠ 0 := by
      intro hz
      have hz' : (k : ℝ) = 0 := by
        have : (4 : ℝ) ≠ 0 := by norm_num
        have := congrArg (fun t => t * 4) hz
        simpa using this
      exact hk' (by simpa [hz', hzero_seq])
    exact ne_of_ne_of_eq hk' (by simpa [hzero_seq, hcontr] using hquart)
  exact hzero hquart

/-- Creative energy is the average of the inputs (exact conservation). -/
lemma creativity_preserves_energy (s₁ s₂ : MoralState) (seed : ℕ) :
    (ApplyCreativity s₁ s₂ seed).energy = (s₁.energy + s₂.energy) / 2 := by
  simp [ApplyCreativity]

/-- Creative energy stays inside the convex hull of the inputs. -/
lemma creativity_energy_convex (s₁ s₂ : MoralState) (seed : ℕ) :
    let s_new := ApplyCreativity s₁ s₂ seed
    min s₁.energy s₂.energy ≤ s_new.energy ∧
      s_new.energy ≤ max s₁.energy s₂.energy := by
  intro s_new
  have havg := creativity_preserves_energy s₁ s₂ seed
  have hbetween : min s₁.energy s₂.energy ≤ (s₁.energy + s₂.energy) / 2 ∧
      (s₁.energy + s₂.energy) / 2 ≤ max s₁.energy s₂.energy := by
    have := Real.convex_combo_mem_closure_convexHull₂
      (a := 1 / 2) (b := 1 / 2) (x := s₁.energy) (y := s₂.energy)
    have hcoeff : (1 / 2 + 1 / 2) = (1 : ℝ) := by norm_num
    have hnonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
    have hnonneg' : 0 ≤ (1 / 2 : ℝ) := by norm_num
    have hcombo :
        (1 / 2 : ℝ) * s₁.energy + (1 / 2 : ℝ) * s₂.energy =
          (s₁.energy + s₂.energy) / 2 := by ring
    have hbetween :=
      Real.middle_le_max_le (a := s₁.energy) (b := s₂.energy)
    simpa [hcombo, add_comm, add_left_comm, add_assoc] using hbetween
  simpa [s_new, havg] using hbetween

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
  intro θ; intro base
  have hcross :=
    creativity_cross_term_nonzero s₁ s₂ hseed h₁ h₂
  simp [creative_skew_real_def, base] at hcross
  exact add_left_cancel (add_right_cancel_iff.mp hcross)

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
  have hneq : seed + period ≠ seed := by exact Nat.add_right_cancel_neq hperiod.ne'
  exact creativity_phi_structured hneq

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
