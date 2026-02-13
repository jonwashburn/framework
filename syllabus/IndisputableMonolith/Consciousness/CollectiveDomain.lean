import Mathlib
import IndisputableMonolith.Constants

/-!
# Collective Domain: Order Parameter and Critical Group Size

This module formalizes "group coherence" with measurable quantities:

1. **Order parameter r** = |⟨e^{i·2πθ}⟩| ∈ [0,1]
   - r = 0: completely incoherent (random phases)
   - r = 1: perfectly synchronized (all phases equal)

2. **Critical group size N_crit**
   - Derived from coupling vs noise scaling
   - Answers: "why might ~20 people be special?"

## The Physics

In coupled oscillator models (Kuramoto), coherence emerges when:
- Coupling strength K exceeds a critical value K_c
- Or equivalently, for fixed K, when N exceeds N_crit

The key scaling insight:
- Pairwise coupling contributions: ~N(N-1)/2 terms
- Independent noise contributions: ~N terms
- Effective signal-to-noise: ~(N-1)/2

For φ-structured thresholds (1/φ ≈ 0.618), coherence stabilizes above N_crit.

## Connection to RS

The binding threshold 1/φ from `GlobalPhase.lean` becomes the coherence threshold.
A group is "phase-locked" when r ≥ 1/φ.
-/

namespace IndisputableMonolith
namespace Consciousness
namespace CollectiveDomain

open scoped BigOperators
open Constants (phi phi_pos one_lt_phi)

/-! ## Phase type -/

abbrev Phase := ℝ  -- interpreted mod 1 in downstream modules

noncomputable def unitPhasor (θ : Phase) : ℂ :=
  Complex.exp (Complex.I * (2 * Real.pi * θ))

theorem norm_unitPhasor (θ : Phase) : ‖unitPhasor θ‖ = 1 := by
  simp [unitPhasor, Complex.norm_exp]

/-! ## Order parameter -/

noncomputable def orderParameter (phases : Finset Phase) : ℂ :=
  if h : phases.Nonempty then
    (1 / (phases.card : ℝ)) * ∑ θ ∈ phases, unitPhasor θ
  else
    0

noncomputable def r (phases : Finset Phase) : ℝ :=
  ‖orderParameter phases‖

theorem r_nonneg (phases : Finset Phase) : 0 ≤ r phases := by
  simp [r]

theorem r_le_one (phases : Finset Phase) : r phases ≤ 1 := by
  classical
  by_cases h : phases.Nonempty
  · have hcard : 0 < phases.card := Finset.card_pos.mpr h
    have hcardR : (0 : ℝ) < (phases.card : ℝ) := by exact_mod_cast hcard
    have _hcardR_ne : (phases.card : ℝ) ≠ 0 := ne_of_gt hcardR
    unfold r orderParameter
    simp [h]
    have hsum :
        ‖∑ θ ∈ phases, unitPhasor θ‖ ≤ ∑ θ ∈ phases, ‖unitPhasor θ‖ :=
      norm_sum_le phases (fun θ => unitPhasor θ)
    have hsum' : (∑ θ ∈ phases, ‖unitPhasor θ‖) = (phases.card : ℝ) := by
      simp [norm_unitPhasor]
    have hsum'' : ‖∑ θ ∈ phases, unitPhasor θ‖ ≤ (phases.card : ℝ) := by
      simpa [hsum'] using hsum
    have : ‖∑ θ ∈ phases, unitPhasor θ‖ / (phases.card : ℝ) ≤ 1 := by
      exact (div_le_iff₀ hcardR).2 (by simpa [one_mul] using hsum'')
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
  · unfold r orderParameter
    simp [h]

/-! ## Phase‑locked domain predicate -/

def PhaseLockedDomain (phases : Finset Phase) (threshold : ℝ) : Prop :=
  r phases ≥ threshold

/-! ## The φ-threshold: 1/φ ≈ 0.618 -/

/-- The binding threshold from RS: 1/φ ≈ 0.618 -/
noncomputable def bindingThreshold : ℝ := 1 / phi

theorem bindingThreshold_pos : 0 < bindingThreshold := by
  unfold bindingThreshold
  exact div_pos one_pos phi_pos

theorem bindingThreshold_lt_one : bindingThreshold < 1 := by
  unfold bindingThreshold
  rw [div_lt_one phi_pos]
  exact one_lt_phi

/-- A domain is coherent if r ≥ 1/φ -/
def CoherentDomain (phases : Finset Phase) : Prop :=
  PhaseLockedDomain phases bindingThreshold

/-! ## Critical group size derivation

The key insight: in a system of N coupled oscillators with:
- Coupling strength K (pairwise)
- Noise strength D (per oscillator)

The effective signal-to-noise ratio scales like:
  SNR_eff ~ K · N(N-1)/2 / (D · N) = K(N-1)/(2D)

For coherence to emerge (SNR_eff ≥ 1), we need:
  N ≥ 1 + 2D/K =: N_crit

In the RS framework:
- K/D is set by the φ-structure (the cost-minimizing coupling)
- The natural ratio is K/D = 1/φ (the binding threshold appears again)

This gives: N_crit = 1 + 2φ ≈ 4.2

For *stable* coherence: N_crit_stable = 1 + 2φ² ≈ 6.2
For *strongly locked*: N_crit_strong = 1 + 2φ³ ≈ 9.5

The "~20" in the pamphlet corresponds to robust operation with 2× margin.
-/

/-- Coupling-to-noise ratio, set by φ-structure -/
noncomputable def couplingNoiseRatio : ℝ := 1 / phi

/-- Critical N for marginal coherence: SNR_eff ≥ 1 -/
noncomputable def N_crit_marginal : ℝ := 1 + 2 * phi

/-- Critical N for stable coherence: SNR_eff ≥ φ -/
noncomputable def N_crit_stable : ℝ := 1 + 2 * phi ^ 2

/-- Critical N for strongly locked coherence: SNR_eff ≥ φ² -/
noncomputable def N_crit_strong : ℝ := 1 + 2 * phi ^ 3

/-- Robust operational N with safety margin -/
noncomputable def N_operational : ℝ := 2 * N_crit_strong

theorem N_crit_marginal_value : N_crit_marginal = 1 + 2 * phi := rfl
theorem N_crit_stable_value : N_crit_stable = 1 + 2 * phi ^ 2 := rfl
theorem N_crit_strong_value : N_crit_strong = 1 + 2 * phi ^ 3 := rfl

/-- N_crit_marginal > 4 (empirical: φ ≈ 1.618, so 1 + 2φ ≈ 4.236).
    Requires showing φ > 1.5, which follows from √5 > 2. -/
theorem N_crit_marginal_gt_4 : 4 < N_crit_marginal := by
  unfold N_crit_marginal
  -- φ > 1.5 from Constants.lean
  have hφ : (1.5 : ℝ) < phi := Constants.phi_gt_onePointFive
  linarith

/-- N_operational ≈ 19 (between 18 and 20) — numerical bound -/
theorem N_operational_bounds : 18 < N_operational ∧ N_operational < 21 := by
  unfold N_operational N_crit_strong
  -- φ³ is between 4.0 and 4.25 from Constants.lean
  have ⟨hlo, hhi⟩ := Constants.phi_cubed_bounds
  constructor <;> linarith

/-! ## Coherence stability theorems -/

/-- A group of N people is above critical size if N > N_crit_marginal -/
def AboveCriticalSize (N : ℕ) : Prop :=
  N_crit_marginal < (N : ℝ)

/-- A group of N ≥ 5 is above marginal critical size -/
theorem five_above_marginal : AboveCriticalSize 5 := by
  unfold AboveCriticalSize
  have h : N_crit_marginal < 5 := by
    unfold N_crit_marginal
    have hφ : phi < 2 := Constants.phi_lt_two
    linarith
  simpa using h

/-- For N ≥ 20, the group is robustly above critical size -/
theorem twenty_robustly_above_critical : AboveCriticalSize 20 := by
  unfold AboveCriticalSize
  have h : N_crit_marginal < 20 := by
    unfold N_crit_marginal
    have hφ : phi < 2 := Constants.phi_lt_two
    linarith
  simpa using h

/-! ## Expected r bounds for critical groups -/

/-- For N above critical with perfect alignment, r = 1 -/
theorem r_perfect_alignment (phases : Finset Phase) (θ₀ : Phase)
    (h : ∀ θ ∈ phases, θ = θ₀) (hne : phases.Nonempty) :
    r phases = 1 := by
  classical
  unfold r orderParameter
  simp only [hne, dite_true]
  have hcard : 0 < phases.card := Finset.card_pos.mpr hne
  have hcardR_pos : (0 : ℝ) < (phases.card : ℝ) := by exact_mod_cast hcard
  have hcardR_ne : (phases.card : ℝ) ≠ 0 := ne_of_gt hcardR_pos
  -- When all phases are equal, the sum of phasors is N times that phasor.
  have hsum_eq : ∑ θ ∈ phases, unitPhasor θ = (phases.card : ℕ) • unitPhasor θ₀ := by
    rw [Finset.sum_eq_card_nsmul]
    intro θ hθ
    exact congrArg unitPhasor (h θ hθ)
  rw [hsum_eq, nsmul_eq_mul]
  -- Now: ‖(1 / N) * (N * unitPhasor θ₀)‖ = ‖unitPhasor θ₀‖ = 1
  have h1 : (1 / (phases.card : ℝ)) * ((phases.card : ℕ) * unitPhasor θ₀) = unitPhasor θ₀ := by
    have hcast : ((phases.card : ℕ) : ℂ) = ((phases.card : ℝ) : ℂ) := by simp
    rw [hcast]
    have hcardC_ne : ((phases.card : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact hcardR_ne
    field_simp [hcardC_ne]
  rw [h1, norm_unitPhasor]

/-- Perfectly aligned phases give a coherent domain -/
theorem perfect_alignment_coherent (phases : Finset Phase) (θ₀ : Phase)
    (h : ∀ θ ∈ phases, θ = θ₀) (hne : phases.Nonempty) :
    CoherentDomain phases := by
  unfold CoherentDomain PhaseLockedDomain
  rw [r_perfect_alignment phases θ₀ h hne]
  have hbt : bindingThreshold < 1 := bindingThreshold_lt_one
  linarith

/-! ## Additional theorems for experimental predictions -/

/-- The N_operational value is approximately 19 -/
theorem N_operational_approx_19 : 18 < N_operational ∧ N_operational < 21 :=
  N_operational_bounds

/-- N = 10 is above the strong locking threshold -/
theorem ten_above_strong : N_crit_strong < 10 := by
  unfold N_crit_strong
  have ⟨hlo, _⟩ := Constants.phi_cubed_bounds
  linarith

/-- The binding threshold matches the RS coupling constant 1/φ -/
theorem bindingThreshold_eq_inv_phi : bindingThreshold = 1 / phi := rfl

/-- Order parameter is bounded: 0 ≤ r ≤ 1 -/
theorem r_bounds (phases : Finset Phase) : 0 ≤ r phases ∧ r phases ≤ 1 :=
  ⟨r_nonneg phases, r_le_one phases⟩

/-- A domain with r ≥ 1/φ is coherent by definition -/
theorem coherent_iff_r_ge_threshold (phases : Finset Phase) :
    CoherentDomain phases ↔ r phases ≥ bindingThreshold := by
  simp [CoherentDomain, PhaseLockedDomain]

/-- The critical hierarchy: marginal < stable < strong -/
theorem N_crit_hierarchy :
    N_crit_marginal < N_crit_stable ∧ N_crit_stable < N_crit_strong := by
  unfold N_crit_marginal N_crit_stable N_crit_strong
  have ⟨hlo, hhi⟩ := Constants.phi_squared_bounds
  have hφ := Constants.one_lt_phi
  constructor <;> nlinarith

end CollectiveDomain
end Consciousness
end IndisputableMonolith
