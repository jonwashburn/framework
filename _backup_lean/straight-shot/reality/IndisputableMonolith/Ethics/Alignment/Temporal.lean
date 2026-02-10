import Mathlib
import IndisputableMonolith.Ethics.Core

namespace IndisputableMonolith
namespace Ethics
namespace Alignment

structure TemporalPolicy where
  maxWindow : Nat := 8
  carryZero : Bool := True

def concatMicro (m n : Microcycle) : Microcycle :=
  { start := m.start, steps := m.steps ++ n.steps }

lemma within_concat (m n : Microcycle) (TP : TemporalPolicy) :
  (m.steps.length + n.steps.length ≤ TP.maxWindow) →
  (concatMicro m n).steps.length ≤ TP.maxWindow := by
  intro h; unfold concatMicro; simpa [List.length_append] using h

lemma justice_concat (m n : Microcycle) :
  JusticeTimely8P m → JusticeTimely8P n → JusticeTimely8P (concatMicro m n) := by
  intro hm hn; unfold JusticeTimely8P concatMicro at *
  rcases hm with ⟨hmLen, hmAcc⟩; rcases hn with ⟨hnLen, hnAcc⟩
  refine And.intro ?len ?acc
  · exact by decide
  · intro p hp; have := List.mem_append.mp hp; cases this with
    | inl hL => exact hmAcc p hL
    | inr hR => exact hnAcc p hR

lemma temperance_concat (m n : Microcycle) :
  TemperanceCapP m → TemperanceCapP n → TemperanceCapP (concatMicro m n) := by
  intro hm hn; unfold TemperanceCapP concatMicro at *; intro p hp
  have := List.mem_append.mp hp; cases this with
  | inl hL => exact hm p hL
  | inr hR => exact hn p hR

lemma reciprocity_concat (m n : Microcycle) :
  ReciprocitySigma0P m → ReciprocitySigma0P n → ReciprocitySigma0P (concatMicro m n) := by
  intros; simp [ReciprocitySigma0P]

lemma publish_concat_of_exec (TP : TemporalPolicy) (m n : Microcycle)
  (hex : ∃ a ds, exec (concatMicro m n) = some (a, ds))
  (hS : ∀ a ds, exec (concatMicro m n) = some (a, ds) → Stable1FlipP ds)
  (hA : ∀ a ds, exec (concatMicro m n) = some (a, ds) → a.val = 0)
  (hJm : JusticeTimely8P m) (hJn : JusticeTimely8P n)
  (hRm : ReciprocitySigma0P m) (hRn : ReciprocitySigma0P n)
  (hTm : TemperanceCapP m) (hTn : TemperanceCapP n)
  (hlen : (m.steps.length + n.steps.length ≤ TP.maxWindow)) :
  PublishP (concatMicro m n) := by
  classical
  rcases hex with ⟨a, ds, hExec⟩
  refine ⟨a, ds, hExec, ?close, ?stable, ?justice, ?recr, ?temp⟩
  · exact hA a ds hExec
  · exact hS a ds hExec
  · have := justice_concat m n hJm hJn; exact this
  · exact reciprocity_concat m n hRm hRn
  · exact temperance_concat m n hTm hTn

end Alignment
end Ethics
end IndisputableMonolith


