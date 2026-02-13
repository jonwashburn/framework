import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Token.WTokenId
import IndisputableMonolith.Token.WTokenBasis

/-!
# Resonance (modality-uniform coupling spec)

This file formalizes the **clean mathematical contract** behind the “Resonance Condition”:

1. Every modality (text/audio/sensors/...) must produce the same kind of object:
   a probability vector on the **20 canonical WToken IDs**.
2. A hypothesis meaning (a chord `ψ : Fin 8 → ℂ`) induces its own probability vector
   via a fixed measurement map.
3. The modality-uniform coupling operator `⊕` is “ratio + J-cost”:

   `r_w = (p_w + ε) / (q_w + ε)` and `E = (1/20) * Σ_w J(r_w)`.

This matches the Noa training direction: “amortize argmin everywhere” means learning
an encoder that outputs a chord which minimizes this same energy, independent of
whether the input was text, audio, or sensors — only the **evidence extractor**
changes with modality.

Important hygiene:
- We keep modality front-ends abstract (they are implementations, not RS axioms).
- We include a small `ε > 0` smoothing parameter so the ratio is always defined.
- We do **not** claim existence/uniqueness of minimizers here; we define the target predicate.
-/

namespace IndisputableMonolith
namespace LightLanguage
namespace Resonance

open scoped BigOperators

/-! ## Core carrier types -/

/-- A ULL chord: an 8-tick complex phase register. -/
abbrev Chord : Type := Fin 8 → ℂ

/-! ## Simplex (probability vectors) -/

/-- A probability vector on a finite type. -/
structure Simplex (α : Type) [Fintype α] where
  /-- The underlying function `α → ℝ`. -/
  p : α → ℝ
  /-- Nonnegativity. -/
  nonneg : ∀ a, 0 ≤ p a
  /-- Total mass is 1. -/
  sum_eq_one : (∑ a, p a) = 1

attribute [simp] Simplex.sum_eq_one

namespace Simplex

variable {α : Type} [Fintype α]

@[simp] lemma nonneg_apply (x : Simplex α) (a : α) : 0 ≤ x.p a :=
  x.nonneg a

end Simplex

/-! ## Canonical token universe -/

open Token

/-- The canonical 20-token index set. -/
abbrev TokenId : Type := Token.WTokenId

instance : Fintype TokenId := inferInstance
instance : Nonempty TokenId := ⟨Token.WTokenId.W0_Origin⟩

/-! ## Chord → token evidence (measurement) -/

namespace Measurement

open Token.WTokenId

/-- Overlap magnitude \( |\langle W_w, \psi \rangle|^2 \) using the current basis model. -/
noncomputable def overlap (ψ : Chord) (w : TokenId) : ℝ :=
  Complex.normSq (Token.WTokenId.innerProduct8 (Token.WTokenId.basisOfId w) ψ)

lemma overlap_nonneg (ψ : Chord) (w : TokenId) : 0 ≤ overlap ψ w := by
  simp [overlap, Complex.normSq_nonneg]

/-- Smoothed measurement distribution \(M_ε(\psi)\) on the 20 tokens.

We use `ε > 0` to avoid the “all overlaps zero” degeneracy: the denominator is
always strictly positive. -/
noncomputable def measure (ε : ℝ) (hε : 0 < ε) (ψ : Chord) : Simplex TokenId := by
  classical
  -- Numerators are `overlap + ε`.
  let num : TokenId → ℝ := fun w => overlap ψ w + ε
  let Z : ℝ := ∑ w : TokenId, num w
  have hnum_nonneg : ∀ w : TokenId, 0 ≤ num w := by
    intro w
    have : 0 ≤ overlap ψ w := overlap_nonneg ψ w
    linarith
  have hsum_overlap_nonneg : 0 ≤ (∑ w : TokenId, overlap ψ w) := by
    refine Finset.sum_nonneg ?_
    intro w _hw
    exact overlap_nonneg ψ w
  have hcard_pos : 0 < (Fintype.card TokenId : ℝ) := by
    -- `TokenId` is nonempty (20 constructors), hence card > 0.
    exact_mod_cast Fintype.card_pos
  have hZ_pos : 0 < Z := by
    -- Z = (∑ overlap) + card*ε, and card*ε > 0.
    have hZ_eq : Z = (∑ w : TokenId, overlap ψ w) + (Fintype.card TokenId : ℝ) * ε := by
      -- Expand `Z` and split the finite sum.
      simp [Z, num, Finset.sum_add_distrib, Finset.sum_const]
    have hcardeps_pos : 0 < (Fintype.card TokenId : ℝ) * ε := by
      exact mul_pos hcard_pos hε
    have hcardeps_le : (Fintype.card TokenId : ℝ) * ε ≤ Z := by
      -- since `∑ overlap ≥ 0`, we have `card*ε ≤ (∑ overlap) + card*ε = Z`.
      rw [hZ_eq]
      exact le_add_of_nonneg_left hsum_overlap_nonneg
    exact lt_of_lt_of_le hcardeps_pos hcardeps_le
  have hZ_ne : Z ≠ 0 := ne_of_gt hZ_pos

  refine
    { p := fun w => num w / Z
      nonneg := ?_
      sum_eq_one := ?_ }
  · intro w
    have hnum : 0 ≤ num w := hnum_nonneg w
    exact div_nonneg hnum (le_of_lt hZ_pos)
  · -- Sum: (∑ num/Z) = (1/Z) * ∑ num = 1.
    have : (∑ w : TokenId, num w / Z) = (1 / Z) * (∑ w : TokenId, num w) := by
      -- rewrite division as multiplication by `Z⁻¹` and factor it out of the finite sum
      simp [div_eq_mul_inv]
      -- Goal: ∑ w, num w * Z⁻¹ = (∑ w, num w) * Z⁻¹
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (Finset.sum_mul (s := (Finset.univ : Finset TokenId)) (f := num) (a := Z⁻¹)).symm
    -- Now `(1/Z) * Z = 1`.
    -- Note: `Z = ∑ num` by definition.
    have hZ_def : Z = (∑ w : TokenId, num w) := rfl
    -- Finish.
    calc
      (∑ w : TokenId, num w / Z)
          = (1 / Z) * (∑ w : TokenId, num w) := this
      _ = (1 / Z) * Z := by simp [hZ_def]
      _ = 1 := by field_simp [hZ_ne]

end Measurement

/-! ## Modality interface -/

/-- A modality is anything that can be mapped into a 20-token evidence simplex. -/
structure Modality where
  Signal : Type
  evidence : Signal → Simplex TokenId

namespace Modality

/-- Text modality (abstract): evidence extractor is provided externally. -/
def Text (evidence : String → Simplex TokenId) : Modality :=
  { Signal := String, evidence := evidence }

/-- Audio modality (abstract signal type): evidence extractor is provided externally. -/
def Audio (Signal : Type) (evidence : Signal → Simplex TokenId) : Modality :=
  { Signal := Signal, evidence := evidence }

/-- Sensor modality (abstract signal type): evidence extractor is provided externally. -/
def Sensors (Signal : Type) (evidence : Signal → Simplex TokenId) : Modality :=
  { Signal := Signal, evidence := evidence }

end Modality

/-! ## The coupling operator (⊕) and resonance energy -/

open Cost

/-- Coupling ratios \( (p_w + ε)/(q_w + ε) \) for a modality evidence vector and a chord. -/
noncomputable def couplingRatios
    (ε : ℝ) (hε : 0 < ε)
    (M : Modality) (s : M.Signal) (ψ : Chord) : TokenId → ℝ :=
  let p := (M.evidence s).p
  let q := (Measurement.measure ε hε ψ).p
  fun w => (p w + ε) / (q w + ε)

/-- Resonance energy (modality-uniform):

\[
E(S,\psi) = \frac{1}{20}\sum_{w} J\!\left(\frac{p_w(S)+\varepsilon}{q_w(\psi)+\varepsilon}\right)
\]

where `p = evidence(S)` and `q = measure(ψ)`. -/
noncomputable def resonanceEnergy
    (ε : ℝ) (hε : 0 < ε)
    (M : Modality) (s : M.Signal) (ψ : Chord) : ℝ :=
  let r := couplingRatios ε hε M s ψ
  (1 / (Fintype.card TokenId : ℝ)) * ∑ w : TokenId, Jcost (r w)

/-! ## “Argmin” as a predicate (what we amortize) -/

/-- `ψ` is a resonance minimizer for signal `s` (with smoothing `ε`). -/
def IsResonanceMinimizer
    (ε : ℝ) (hε : 0 < ε)
    (M : Modality) (s : M.Signal) (ψ : Chord) : Prop :=
  ∀ ψ' : Chord, resonanceEnergy ε hε M s ψ ≤ resonanceEnergy ε hε M s ψ'

/-- An amortizer is any learned encoder that maps signals to chords. -/
abbrev Amortizer (M : Modality) : Type := M.Signal → Chord

/-- Exact amortization target: the amortizer always outputs a minimizer. -/
def IsExactAmortizer
    (ε : ℝ) (hε : 0 < ε)
    (M : Modality) (f : Amortizer M) : Prop :=
  ∀ s : M.Signal, IsResonanceMinimizer ε hε M s (f s)

/-! ## Modality invariance lemma (energy depends only on evidence) -/

theorem resonanceEnergy_depends_only_on_evidence
    (ε : ℝ) (hε : 0 < ε)
    (M₁ M₂ : Modality)
    (s₁ : M₁.Signal) (s₂ : M₂.Signal)
    (ψ : Chord)
    (hE : M₁.evidence s₁ = M₂.evidence s₂) :
    resonanceEnergy ε hε M₁ s₁ ψ = resonanceEnergy ε hε M₂ s₂ ψ := by
  -- By definitional unfolding: only `evidence` differs across modalities.
  simp [resonanceEnergy, couplingRatios, hE]

/-! ## Physics-like theorems -/

/-- Resonance energy is non-negative. -/
theorem resonanceEnergy_nonneg
    (ε : ℝ) (hε : 0 < ε)
    (M : Modality) (s : M.Signal) (ψ : Chord) :
    0 ≤ resonanceEnergy ε hε M s ψ := by
  unfold resonanceEnergy
  apply mul_nonneg
  · apply one_div_nonneg.mpr
    -- `card TokenId ≥ 0` (as a Nat), hence also nonnegative as a real.
    exact_mod_cast (Nat.zero_le (Fintype.card TokenId))
  · apply Finset.sum_nonneg
    intro w _
    apply Jcost_nonneg
    -- Show ratio is positive
    unfold couplingRatios
    let p := (M.evidence s).p
    let q := (Measurement.measure ε hε ψ).p
    have hp : 0 ≤ p w := (M.evidence s).nonneg w
    have hq : 0 ≤ q w := (Measurement.measure ε hε ψ).nonneg w
    apply div_pos
    · linarith
    · linarith

/-- Perfect resonance (E=0) implies evidence matches measurement exactly (up to ε ratio).
    Since J(x)=0 ↔ x=1, E=0 ↔ p_w = q_w for all w. -/
theorem resonanceEnergy_zero_iff
    (ε : ℝ) (hε : 0 < ε)
    (M : Modality) (s : M.Signal) (ψ : Chord) :
    resonanceEnergy ε hε M s ψ = 0 ↔
      (M.evidence s).p = (Measurement.measure ε hε ψ).p := by
  unfold resonanceEnergy
  -- Factor out the positive constant 1/20
  have h_card_pos : 0 < (Fintype.card TokenId : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have h_const_pos : 0 < 1 / (Fintype.card TokenId : ℝ) :=
    one_div_pos.mpr h_card_pos
  rw [mul_eq_zero]
  simp only [h_const_pos.ne', false_or]
  -- Sum of nonnegatives is zero iff all terms are zero
  constructor
  · intro h_sum
    have h_term_zero : ∀ w, Jcost (couplingRatios ε hε M s ψ w) = 0 := by
      intro w
      rw [Finset.sum_eq_zero_iff_of_nonneg] at h_sum
      · exact h_sum w (Finset.mem_univ w)
      · intro w _
        apply Jcost_nonneg
        unfold couplingRatios
        let p := (M.evidence s).p
        let q := (Measurement.measure ε hε ψ).p
        apply div_pos <;> linarith [(M.evidence s).nonneg w, (Measurement.measure ε hε ψ).nonneg w]
    ext w
    specialize h_term_zero w
    have h_ratio_one : couplingRatios ε hε M s ψ w = 1 := by
      apply Jcost_zero_iff_one _ (h_term_zero)
      unfold couplingRatios
      let p := (M.evidence s).p
      let q := (Measurement.measure ε hε ψ).p
      apply div_pos <;> linarith [(M.evidence s).nonneg w, (Measurement.measure ε hε ψ).nonneg w]
    -- (p+ε)/(q+ε) = 1 → p+ε = q+ε → p=q
    unfold couplingRatios at h_ratio_one
    let p := (M.evidence s).p
    let q := (Measurement.measure ε hε ψ).p
    have h_denom_ne_zero : q w + ε ≠ 0 := by
      have : 0 < q w + ε := add_pos_of_nonneg_of_pos ((Measurement.measure ε hε ψ).nonneg w) hε
      exact this.ne'
    rw [div_eq_one_iff_eq h_denom_ne_zero] at h_ratio_one
    linarith
  · intro h_eq
    -- If p=q, then ratio=1, J(1)=0, sum=0
    apply Finset.sum_eq_zero
    intro w _
    unfold couplingRatios
    rw [h_eq]
    rw [div_self]
    · exact Jcost_unit0
    · have : 0 < (Measurement.measure ε hε ψ).p w + ε :=
        add_pos_of_nonneg_of_pos ((Measurement.measure ε hε ψ).nonneg w) hε
      exact this.ne'

/-- Measurement is gauge invariant: rotating the chord by a global phase
    does not change the evidence vector. -/
theorem measurement_gauge_invariant
    (ε : ℝ) (hε : 0 < ε)
    (ψ : Chord) (θ : ℝ) :
    Measurement.measure ε hε (fun t => Complex.exp (Complex.I * θ) * ψ t) =
    Measurement.measure ε hε ψ := by
  -- It suffices to show overlaps are invariant
  have h_overlap : ∀ w, Measurement.overlap (fun t => Complex.exp (Complex.I * θ) * ψ t) w =
                        Measurement.overlap ψ w := by
    intro w
    unfold Measurement.overlap
    -- <B, e^{iθ} ψ> = e^{iθ} <B, ψ>
    have h_inner : Token.WTokenId.innerProduct8 (Token.WTokenId.basisOfId w)
                     (fun t => Complex.exp (Complex.I * θ) * ψ t) =
                   Complex.exp (Complex.I * θ) *
                   Token.WTokenId.innerProduct8 (Token.WTokenId.basisOfId w) ψ := by
      -- Reuse the general scaling lemma for the right argument.
      simpa using
        (Token.WTokenId.innerProduct8_scale_right
          (c := Complex.exp (Complex.I * θ))
          (v₁ := Token.WTokenId.basisOfId w)
          (v₂ := ψ))
    rw [h_inner]
    -- |e^{iθ} z|² = |e^{iθ}|² |z|² = 1 * |z|²
    rw [Complex.normSq_mul]
    have h_norm_exp : Complex.normSq (Complex.exp (Complex.I * θ)) = 1 := by
      -- `‖exp(iθ)‖ = 1`, hence `normSq = ‖·‖^2 = 1`.
      have h_norm : ‖Complex.exp (Complex.I * θ)‖ = 1 := by
        simpa using (Complex.abs_exp_it_number (theta := θ))
      rw [Complex.normSq_eq_norm_sq]
      simp [h_norm]
    rw [h_norm_exp, one_mul]
  -- If overlaps match, measures match (measure is a function of overlaps)
  unfold Measurement.measure
  simp_rw [h_overlap]

/-- Symmetry of J-cost implies symmetry of resonance strain with respect to the ratio.
    J(r) = J(1/r). -/
theorem resonanceEnergy_symm_ratio
    (ε : ℝ) (hε : 0 < ε)
    (M : Modality) (s : M.Signal) (ψ : Chord) :
    resonanceEnergy ε hε M s ψ =
    (1 / (Fintype.card TokenId : ℝ)) * ∑ w : TokenId, Jcost ((couplingRatios ε hε M s ψ w)⁻¹) := by
  classical
  -- Inline the `let r := couplingRatios ...` on the left.
  unfold resonanceEnergy
  simp
  -- Now apply `J` symmetry pointwise inside the finite sum.
  have hsum :
      (∑ w : TokenId, Jcost (couplingRatios ε hε M s ψ w)) =
        ∑ w : TokenId, Jcost ((couplingRatios ε hε M s ψ w)⁻¹) := by
    refine Finset.sum_congr rfl ?_
    intro w _
    apply Jcost_symm
    -- ratio is positive
    unfold couplingRatios
    let p := (M.evidence s).p
    let q := (Measurement.measure ε hε ψ).p
    apply div_pos <;> linarith [(M.evidence s).nonneg w, (Measurement.measure ε hε ψ).nonneg w]
  -- Transport across the shared scalar factor.
  simpa [hsum]

end Resonance
end LightLanguage
end IndisputableMonolith
