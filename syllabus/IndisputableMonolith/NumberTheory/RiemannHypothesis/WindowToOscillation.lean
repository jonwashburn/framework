import IndisputableMonolith.NumberTheory.RiemannHypothesis.LocalToGlobalWedge
import Mathlib.MeasureTheory.Measure.Stieltjes

/-!
# Riemann Hypothesis (BRF route): window/measure control → oscillation control

This file targets the **bridge step** immediately preceding Lemma
`local-to-global-wedge` in `docs/primes/Riemann-proofs/Riemann-active.txt`:

> a window (test-function) bound for the positive distribution `-w'`
> implies a bound on the essential oscillation
> `Δ_I(w) = essSup_I w - essInf_I w`.

In Lean, the most robust way to formalize the “integration by parts” aspect is to model `-w'`
as a **Stieltjes measure** attached to a monotone right-continuous function. Concretely:

- assume `w : ℝ → ℝ` is **antitone** (nonincreasing) and **right-continuous**;
- then `g := fun t ↦ -w t` is monotone and right-continuous, hence defines a Stieltjes measure `μ`;
- the mass `μ(Ioo a b)` is exactly the **drop** `w a - leftLim w b` (as an `ENNReal.ofReal`);
- for antitone `w`, this drop controls the essential oscillation on `Icc a b`.

This is a clean, reusable interface: the analytic RH work provides bounds on the Stieltjes mass
on Whitney intervals; this file turns them into `oscOn` bounds, which then feed into the already
formalized local-to-global wedge lemma.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace RiemannHypothesis

open scoped Real Topology
open MeasureTheory Filter Set
open scoped ENNReal

/-!
## Plateau/mass extraction (B1 bridge)

If `μ` is a measure, `φ ≥ 0` is a window function, and `φ` has a pointwise lower bound `c` on a
set `s`, then bounding `∫ φ dμ` controls `μ(s)`:

`(∀ x∈s, c ≤ φ x)` and `(∫ φ dμ ≤ A)`  ⇒  `μ(s) ≤ A / c`.

This is the Lean version of the “plateau ⇒ mass extraction” step used in the active certificate.
-/

namespace Plateau

theorem measure_le_lintegral_div_of_forall_le_on {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : Set α} (hs : MeasurableSet s) {φ : α → ℝ≥0∞} {c : ℝ≥0∞}
    (hc0 : c ≠ 0) (hcTop : c ≠ ⊤) (hle : ∀ x, x ∈ s → c ≤ φ x) :
    μ s ≤ (∫⁻ x, φ x ∂μ) / c := by
  -- First show `c * μ s ≤ ∫ φ dμ` by integrating the indicator of the constant `c` over `s`.
  have h_ind : s.indicator (fun _ : α => c) ≤ φ := by
    intro x
    by_cases hx : x ∈ s
    · simpa [hx] using hle x hx
    · -- outside `s`, the indicator is `0` and `0 ≤ φ x`.
      simp [hx]
  have hmul : c * μ s ≤ ∫⁻ x, φ x ∂μ := by
    calc
      c * μ s = ∫⁻ x, s.indicator (fun _ : α => c) x ∂μ := by
        simpa using (lintegral_indicator_const (μ := μ) hs c).symm
      _ ≤ ∫⁻ x, φ x ∂μ := lintegral_mono h_ind
  -- Divide by `c` using `ENNReal.le_div_iff_mul_le`.
  have : μ s ≤ (∫⁻ x, φ x ∂μ) / c :=
    (ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hcTop)).2 (by simpa [mul_comm] using hmul)
  exact this

end Plateau

/-!
## Stieltjes measure for `-w`
-/

/-- The Stieltjes function `t ↦ -w(t)` built from an antitone, right-continuous `w`. -/
noncomputable def stieltjesNeg (w : ℝ → ℝ) (hw : Antitone w)
    (hw_rc : ∀ x, ContinuousWithinAt w (Ici x) x) :
    StieltjesFunction ℝ :=
  { toFun := fun x => -w x
    mono' := by
      intro x y hxy
      have : w y ≤ w x := hw hxy
      exact neg_le_neg this
    right_continuous' := by
      intro x
      simpa using (hw_rc x).neg }

namespace stieltjesNeg

variable {w : ℝ → ℝ} {hw : Antitone w} {hw_rc : ∀ x, ContinuousWithinAt w (Ici x) x}

/-- The Stieltjes measure associated to `t ↦ -w(t)`. -/
noncomputable def μ : Measure ℝ :=
  (stieltjesNeg w hw hw_rc).measure

lemma leftLim_neg_eq_neg_leftLim (w : ℝ → ℝ) (hw : Antitone w) (b : ℝ) :
    Function.leftLim (fun x => -w x) b = - Function.leftLim w b := by
  -- Antitone functions have left limits; use uniqueness of limits and continuity of `neg`.
  have hwlim : Tendsto w (𝓝[<] b) (nhds (Function.leftLim w b)) :=
    Antitone.tendsto_leftLim hw b
  have hne : (𝓝[<] b) ≠ (⊥ : Filter ℝ) := by
    haveI : NeBot (𝓝[<] b) := by infer_instance
    exact (neBot_iff.1 (by infer_instance))
  have hwlim' : Tendsto (fun x => -w x) (𝓝[<] b) (nhds (-Function.leftLim w b)) :=
    hwlim.neg
  exact leftLim_eq_of_tendsto (f := fun x => -w x) (a := b) hne hwlim'

/-- Stieltjes mass on `Ioo a b` equals the phase drop `w a - leftLim w b` (as `ofReal`). -/
lemma measure_Ioo_eq_ofReal_drop (a b : ℝ) :
    (μ (w := w) (hw := hw) (hw_rc := hw_rc)) (Set.Ioo a b)
      = ENNReal.ofReal (w a - Function.leftLim w b) := by
  -- Start from the generic Stieltjes formula.
  let g : StieltjesFunction ℝ := stieltjesNeg w hw hw_rc
  have hIoo : g.measure (Set.Ioo a b) = ENNReal.ofReal (Function.leftLim g b - g a) := by
    simpa using (StieltjesFunction.measure_Ioo (f := g) (a := a) (b := b))
  -- Rewrite `g a = -w a` and `leftLim g b = - leftLim w b`.
  have hLL : Function.leftLim g b = - Function.leftLim w b := by
    -- `g = fun x ↦ -w x`
    simpa [g, stieltjesNeg] using (leftLim_neg_eq_neg_leftLim (w := w) hw b)
  -- Simplify the real expression.
  have : (Function.leftLim g b - g a) = (w a - Function.leftLim w b) := by
    have hga : g a = -w a := by
      simp [g, stieltjesNeg]
    calc
      Function.leftLim g b - g a = Function.leftLim g b - (-w a) := by simpa [hga]
      _ = (-Function.leftLim w b) - (-w a) := by simpa [hLL]
      _ = w a - Function.leftLim w b := by
        simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  -- Finish.
  simpa [μ, g, hIoo, this]

end stieltjesNeg

/-!
## Oscillation control for antitone phases
-/

/-- On a nontrivial interval, an antitone phase has essential oscillation controlled by the
endpoint drop `w a - leftLim w b`. -/
theorem oscOn_Icc_le_drop_of_antitone {w : ℝ → ℝ} (hw : Antitone w) {a b : ℝ} (hab : a < b) :
    oscOn w (Set.Icc a b) ≤ w a - Function.leftLim w b := by
  classical
  let μI : Measure ℝ := volume.restrict (Set.Icc a b)
  have hμI_pos : 0 < μI Set.univ := by
    -- `μI univ = volume (Icc a b) = ofReal (b-a)`, positive for `a<b`.
    simpa [μI, Real.volume_Icc, hab.ne', sub_pos.2 hab] using
      (ENNReal.ofReal_pos.2 (sub_pos.2 hab))

  -- Upper bound on `essSup` via its `sInf` characterization.
  have hsup : essSup w μI ≤ w a := by
    -- Let `S := {c | μI {x | c < w x} = 0}`.
    let S : Set ℝ := {c : ℝ | μI {x : ℝ | c < w x} = 0}
    -- `S` is bounded below by `w b`: if `c < w b` then `{c < w x}` contains the whole interval,
    -- hence has positive measure.
    have hS_bdd : BddBelow S := by
      refine ⟨w b, ?_⟩
      intro c hc
      by_contra hcb
      have hcb' : c < w b := lt_of_not_ge hcb
      have hsubset : Set.Icc a b ⊆ {x : ℝ | c < w x} := by
        intro x hx
        have : w b ≤ w x := hw hx.2
        exact lt_of_lt_of_le hcb' this
      have hpos : 0 < μI {x : ℝ | c < w x} := by
        have : 0 < μI (Set.Icc a b) := by
          -- `μI (Icc a b) = volume (Icc a b)` and is positive when `a<b`.
          simpa [μI, Real.volume_Icc, hab.ne', sub_pos.2 hab] using
            (ENNReal.ofReal_pos.2 (sub_pos.2 hab))
        -- `Icc a b ⊆ {c < w x}` gives positive measure of the larger set.
        exact lt_of_lt_of_le this (measure_mono hsubset)
      -- Contradiction with `c ∈ S`.
      exact (ne_of_gt hpos) (by simpa [S] using hc)
    -- `w a ∈ S` because `w a < w x` never happens on `Icc a b`.
    have hwa : (w a) ∈ S := by
      have hempty : ({x : ℝ | w a < w x} ∩ Set.Icc a b) = (∅ : Set ℝ) := by
        ext x; constructor
        · intro hx
          rcases hx with ⟨hx1, hx2⟩
          have : w x ≤ w a := hw hx2.1
          exact (not_lt_of_ge this hx1).elim
        · intro hx; simpa using hx
      have : μI {x : ℝ | w a < w x} = 0 := by
        -- `μI s = volume (s ∩ Icc a b)` and the intersection is empty.
        simp [μI, Measure.restrict_apply' (hs := measurableSet_Icc), hempty]
      simpa [S] using this
    -- Now apply `essSup_eq_sInf` and the conditional `csInf_le`.
    rw [essSup_eq_sInf (μ := μI) (f := w)]
    -- goal: `sInf S ≤ w a`
    -- `S` is bounded below and nonempty, so we can use `csInf_le`.
    simpa [S] using (csInf_le hS_bdd hwa)

  -- Lower bound on `essInf` via its `sSup` characterization.
  have hinf : Function.leftLim w b ≤ essInf w μI := by
    let T : Set ℝ := {c : ℝ | μI {x : ℝ | w x < c} = 0}
    -- `T` is bounded above by `w a`.
    have hT_bdd : BddAbove T := by
      refine ⟨w a, ?_⟩
      intro c hc
      by_contra hac
      have hac' : w a < c := lt_of_not_ge hac
      have hsubset : Set.Icc a b ⊆ {x : ℝ | w x < c} := by
        intro x hx
        have : w x ≤ w a := hw hx.1
        exact lt_of_le_of_lt this hac'
      have hpos : 0 < μI {x : ℝ | w x < c} := by
        have : 0 < μI (Set.Icc a b) := by
          simpa [μI, Real.volume_Icc, hab.ne', sub_pos.2 hab] using
            (ENNReal.ofReal_pos.2 (sub_pos.2 hab))
        exact lt_of_lt_of_le this (measure_mono hsubset)
      exact (ne_of_gt hpos) (by simpa [T] using hc)
    -- `leftLim w b ∈ T` because `{w x < leftLim w b}` can only occur at the endpoint `b`,
    -- which is a null set for Lebesgue.
    have hLL : (Function.leftLim w b) ∈ T := by
      have hsubset : ({x : ℝ | w x < Function.leftLim w b} ∩ Set.Icc a b) ⊆ ({b} : Set ℝ) := by
        intro x hx
        rcases hx with ⟨hxlt, hxab⟩
        have hxle : x ≤ b := hxab.2
        by_contra hxb
        have hxb' : x < b := lt_of_le_of_ne hxle hxb
        have : Function.leftLim w b ≤ w x := Antitone.leftLim_le (hf := hw) hxb'
        exact (not_lt_of_ge this hxlt).elim
      have : μI {x : ℝ | w x < Function.leftLim w b} = 0 := by
        -- Expand the restricted measure: `μI s = volume (s ∩ Icc a b)`.
        have hb : volume ({b} : Set ℝ) = 0 := by simp
        have hle :
            volume ({x : ℝ | w x < Function.leftLim w b} ∩ Set.Icc a b) ≤ volume ({b} : Set ℝ) :=
          measure_mono hsubset
        have hzero : volume ({x : ℝ | w x < Function.leftLim w b} ∩ Set.Icc a b) = 0 :=
          le_antisymm (le_trans hle (by simpa [hb])) (by simp)
        -- Convert back to `μI`.
        simpa [μI, Measure.restrict_apply' (hs := measurableSet_Icc), Set.inter_assoc,
          Set.inter_left_comm, Set.inter_comm] using hzero
      simpa [T] using this
    -- Apply `essInf_eq_sSup` and `le_csSup`.
    rw [essInf_eq_sSup (μ := μI) (f := w)]
    -- goal: `leftLim w b ≤ sSup T`
    simpa [T] using (le_csSup hT_bdd hLL)

  -- Combine into the oscillation bound.
  dsimp [oscOn]
  nlinarith [hsup, hinf]

/-!
## From a Stieltjes mass bound to an `oscOn` bound
-/

/-- If the Stieltjes mass of `t ↦ -w(t)` on `Ioo a b` is at most `π·Υ`, then the essential
oscillation of `w` on `Icc a b` is at most `π·Υ`. -/
theorem oscOn_Icc_le_pi_mul_of_stieltjes_Ioo_bound
    {w : ℝ → ℝ} (hw : Antitone w) (hw_rc : ∀ x, ContinuousWithinAt w (Ici x) x)
    {a b Υ : ℝ} (hab : a < b) (hΥ : 0 ≤ Υ)
    (hμ :
      (stieltjesNeg.μ (w := w) (hw := hw) (hw_rc := hw_rc)) (Set.Ioo a b)
        ≤ ENNReal.ofReal (Real.pi * Υ)) :
    oscOn w (Set.Icc a b) ≤ Real.pi * Υ := by
  have hoscle : oscOn w (Set.Icc a b) ≤ w a - Function.leftLim w b :=
    oscOn_Icc_le_drop_of_antitone (w := w) hw hab
  have hdrop : w a - Function.leftLim w b ≤ Real.pi * Υ := by
    have hnonneg : 0 ≤ Real.pi * Υ := mul_nonneg (le_of_lt Real.pi_pos) hΥ
    have hmass :
        ENNReal.ofReal (w a - Function.leftLim w b) ≤ ENNReal.ofReal (Real.pi * Υ) := by
      -- rewrite the LHS using the Stieltjes drop formula
      simpa [stieltjesNeg.measure_Ioo_eq_ofReal_drop (w := w) (hw := hw) (hw_rc := hw_rc) a b]
        using hμ
    exact (ENNReal.ofReal_le_ofReal_iff hnonneg).1 hmass
  exact le_trans hoscle hdrop

/-!
## B1: window bound + plateau ⇒ `oscOn` bound

This is the “plateau/mass-extraction” bridge: if a window `φ` is bounded below by `c>0` on
`Ioo a b`, and `∫ φ dμ ≤ D`, then `μ(Ioo a b) ≤ D / c`. For the Stieltjes measure `μ = d(-w)`,
this yields an `oscOn` bound on `Icc a b`.
-/

theorem oscOn_Icc_le_div_of_window_lintegral_bound
    {w : ℝ → ℝ} (hw : Antitone w) (hw_rc : ∀ x, ContinuousWithinAt w (Ici x) x)
    {a b D c : ℝ} (hab : a < b) (hD : 0 ≤ D) (hc : 0 < c)
    {φ : ℝ → ℝ≥0∞}
    (hφ_lower : ∀ t, t ∈ Set.Ioo a b → ENNReal.ofReal c ≤ φ t)
    (hlin : ∫⁻ t, φ t ∂(stieltjesNeg.μ (w := w) (hw := hw) (hw_rc := hw_rc))
              ≤ ENNReal.ofReal D) :
    oscOn w (Set.Icc a b) ≤ D / c := by
  have hc0 : (ENNReal.ofReal c) ≠ 0 := by
    have : 0 < ENNReal.ofReal c := (ENNReal.ofReal_pos.2 hc)
    exact (ne_of_gt this)
  have hcTop : (ENNReal.ofReal c) ≠ ⊤ := ENNReal.ofReal_ne_top
  -- Mass extraction: `μ(Ioo a b) ≤ (∫ φ dμ) / c`.
  have hmass₁ :
      (stieltjesNeg.μ (w := w) (hw := hw) (hw_rc := hw_rc)) (Set.Ioo a b)
        ≤ (∫⁻ t, φ t ∂(stieltjesNeg.μ (w := w) (hw := hw) (hw_rc := hw_rc))) /
            (ENNReal.ofReal c) := by
    exact Plateau.measure_le_lintegral_div_of_forall_le_on
      (μ := stieltjesNeg.μ (w := w) (hw := hw) (hw_rc := hw_rc))
      (s := Set.Ioo a b) measurableSet_Ioo hc0 hcTop hφ_lower
  have hmass₂ :
      (stieltjesNeg.μ (w := w) (hw := hw) (hw_rc := hw_rc)) (Set.Ioo a b)
        ≤ ENNReal.ofReal (D / c) := by
    -- Combine the mass extraction with the lintegral bound and rewrite `ofReal (D / c)`.
    have hnonneg_c : 0 < c := hc
    have hnonneg_Dc : 0 ≤ D / c := by exact div_nonneg hD (le_of_lt hc)
    have : (∫⁻ t, φ t ∂(stieltjesNeg.μ (w := w) (hw := hw) (hw_rc := hw_rc))) / ENNReal.ofReal c
        ≤ ENNReal.ofReal D / ENNReal.ofReal c := by
      exact ENNReal.div_le_div_right hlin (ENNReal.ofReal c)
    have hrewrite : ENNReal.ofReal (D / c) = ENNReal.ofReal D / ENNReal.ofReal c := by
      simpa using (ENNReal.ofReal_div_of_pos (x := D) (y := c) hnonneg_c)
    have : (stieltjesNeg.μ (w := w) (hw := hw) (hw_rc := hw_rc)) (Set.Ioo a b)
        ≤ ENNReal.ofReal D / ENNReal.ofReal c := le_trans hmass₁ this
    simpa [hrewrite] using this
  -- Convert `μ(Ioo) ≤ ofReal(D/c)` into `oscOn ≤ D/c` using the already-proved drop bound.
  have hoscle : oscOn w (Set.Icc a b) ≤ w a - Function.leftLim w b :=
    oscOn_Icc_le_drop_of_antitone (w := w) hw hab
  have hdrop : w a - Function.leftLim w b ≤ D / c := by
    have hnonneg : 0 ≤ D / c := div_nonneg hD (le_of_lt hc)
    have hmass :
        ENNReal.ofReal (w a - Function.leftLim w b) ≤ ENNReal.ofReal (D / c) := by
      simpa [stieltjesNeg.measure_Ioo_eq_ofReal_drop (w := w) (hw := hw) (hw_rc := hw_rc) a b]
        using hmass₂
    exact (ENNReal.ofReal_le_ofReal_iff hnonneg).1 hmass
  exact le_trans hoscle hdrop

end RiemannHypothesis
end NumberTheory
end IndisputableMonolith
