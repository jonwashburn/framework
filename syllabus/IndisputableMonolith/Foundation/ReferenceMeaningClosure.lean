import IndisputableMonolith.Foundation.Reference

/-!
# Reference Meaning Closure (forced meaning lemmas)

This module isolates a small, reusable fragment of the "meaning is forced" story:

- Meaning is defined as an **argmin** of a reference cost (`Reference.Meaning`).
- For the canonical ratio-induced reference (`ratioReference`), **ratio matching implies meaning**.
- Under an injectivity (identifiability) hypothesis, ratio matching implies **unique** meaning.
- If every symbol-ratio is realized by exactly one object-ratio, then meanings are **globally forced**
  (existence + uniqueness of the argmin, per symbol).

This is intentionally a *method-layer* lemma pack: domains still supply the object space `O`,
ratio maps `ιS, ιO`, and the realization/identifiability hypotheses.
-/

namespace IndisputableMonolith
namespace Foundation
namespace Reference

open scoped Classical

/-!
## General “argmin as a chosen function” helper

`Meaning` in `Foundation.Reference` is a `Prop` (an argmin predicate).
If a domain proves existence of minimizers, we can choose a meaning function by classical choice.
-/

/-- Choose a meaning function from an existence proof of minimizers. -/
noncomputable def meaningChoice {S O : Type}
    (R : ReferenceStructure S O)
    (hex : ∀ s : S, ∃ o : O, Meaning R s o) : S → O :=
  fun s => Classical.choose (hex s)

theorem meaningChoice_spec {S O : Type}
    (R : ReferenceStructure S O)
    (hex : ∀ s : S, ∃ o : O, Meaning R s o) (s : S) :
    Meaning R s (meaningChoice R hex s) :=
  Classical.choose_spec (hex s)

theorem meaningChoice_eq_of_unique {S O : Type}
    (R : ReferenceStructure S O)
    (hex : ∀ s : S, ∃ o : O, Meaning R s o)
    (s : S) (o : O)
    (huniq : ∀ o' : O, Meaning R s o' → o' = o) :
    meaningChoice R hex s = o := by
  apply huniq
  exact meaningChoice_spec R hex s

/-!
## Ratio-reference meaning lemmas
-/

/-- If ratios match, the ratio-induced reference cost is zero, hence the target is a (weak) meaning. -/
theorem meaning_of_ratio_eq {S O : Type}
    (ιS : RatioMap S) (ιO : RatioMap O)
    (s : S) (o : O)
    (h : ιS.ratio s = ιO.ratio o) :
    Meaning (ratioReference S O ιS ιO) s o := by
  intro o'
  have h0 : (ratioReference S O ιS ιO).cost s o = 0 :=
    (ratio_reference_zero_iff S O ιS ιO s o).2 h
  have hnonneg : 0 ≤ (ratioReference S O ιS ιO).cost s o' :=
    (ratioReference S O ιS ιO).nonneg s o'
  linarith

/-- Under identifiability (`ιO.ratio` injective), a ratio match yields a *strict* argmin, hence unique meaning. -/
theorem uniqueMeaning_of_ratio_eq {S O : Type}
    (ιS : RatioMap S) (ιO : RatioMap O)
    (hinj : Function.Injective ιO.ratio)
    (s : S) (o : O)
    (h : ιS.ratio s = ιO.ratio o) :
    UniqueMeaning (ratioReference S O ιS ιO) s o := by
  refine ⟨meaning_of_ratio_eq (ιS := ιS) (ιO := ιO) (s := s) (o := o) h, ?_⟩
  intro o' ho'
  have hcost0 : (ratioReference S O ιS ιO).cost s o = 0 :=
    (ratio_reference_zero_iff S O ιS ιO s o).2 h
  have hne_one : ιS.ratio s / ιO.ratio o' ≠ 1 := by
    intro hdiv
    have ho'_ne0 : ιO.ratio o' ≠ 0 := ne_of_gt (ιO.pos o')
    have hEq : ιS.ratio s = ιO.ratio o' := by
      -- `a / b = 1` rewrites to `a = b` when `b ≠ 0`
      have : ιS.ratio s / ιO.ratio o' = 1 ↔ ιS.ratio s = ιO.ratio o' :=
        div_eq_one_iff_eq ho'_ne0
      exact (this.mp hdiv)
    have : o' = o := by
      apply hinj
      -- `ιO.ratio o' = ιO.ratio o`
      simpa [h] using hEq.symm
    exact ho' this
  have hpos : 0 < (ratioReference S O ιS ιO).cost s o' := by
    have hx : 0 < ιS.ratio s / ιO.ratio o' := div_pos (ιS.pos s) (ιO.pos o')
    -- cost = Jcost( ratio mismatch ) and Jcost > 0 when mismatch ≠ 1
    simpa [ratioReference] using Cost.Jcost_pos_of_ne_one (ιS.ratio s / ιO.ratio o') hx hne_one
  -- strict minimizer: 0 < cost(s,o') and cost(s,o)=0
  linarith

/-!
## Global forcing (existence + uniqueness) as a domain-level closure statement

The following is a clean statement of the “meaning is forced” condition for ratio-reference:
every symbol ratio is realized by *exactly one* object ratio (identifiability).
-/

/-- Domain hypothesis: every symbol ratio is realized by some object. -/
def RatioRealization {S O : Type} (ιS : RatioMap S) (ιO : RatioMap O) : Prop :=
  ∀ s : S, ∃ o : O, ιS.ratio s = ιO.ratio o

/-- If ratios are realized and object ratios are identifiable, then each symbol has a unique meaning. -/
theorem forcedMeaning_of_ratioRealization {S O : Type}
    (ιS : RatioMap S) (ιO : RatioMap O)
    (hinj : Function.Injective ιO.ratio)
    (hreal : RatioRealization ιS ιO) :
    ∀ s : S, ∃! o : O, Meaning (ratioReference S O ιS ιO) s o := by
  intro s
  rcases hreal s with ⟨o, hso⟩
  refine ⟨o, ?_, ?_⟩
  · exact meaning_of_ratio_eq (ιS := ιS) (ιO := ιO) (s := s) (o := o) hso
  · intro o' ho'
    -- Show any minimizer must also have zero cost (since cost at `o` is 0), hence must match ratios, hence equals `o`.
    have hcost0 : (ratioReference S O ιS ιO).cost s o = 0 :=
      (ratio_reference_zero_iff S O ιS ιO s o).2 hso
    have hle : (ratioReference S O ιS ιO).cost s o' ≤ (ratioReference S O ιS ιO).cost s o := ho' o
    have hnonneg : 0 ≤ (ratioReference S O ιS ιO).cost s o' :=
      (ratioReference S O ιS ιO).nonneg s o'
    have hcost0' : (ratioReference S O ιS ιO).cost s o' = 0 := by
      -- 0 ≤ cost(s,o') ≤ cost(s,o)=0
      linarith
    have hratio' : ιS.ratio s = ιO.ratio o' :=
      (ratio_reference_zero_iff S O ιS ιO s o').1 hcost0'
    have : o' = o := by
      apply hinj
      -- `ιO.ratio o' = ιO.ratio o`
      simpa [hso] using hratio'.symm
    exact this

end Reference
end Foundation
end IndisputableMonolith
