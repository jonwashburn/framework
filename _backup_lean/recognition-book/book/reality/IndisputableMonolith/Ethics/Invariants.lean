import Mathlib
import IndisputableMonolith.Ethics.Core

namespace IndisputableMonolith
namespace Ethics
namespace Invariants

def Monotonicity : Prop :=
  ∀ {A : Type} (M : IndisputableMonolith.Ethics.CostModel A)
    (C : IndisputableMonolith.Ethics.Composable M)
    {a₁ a₂ b₁ b₂ : A},
      IndisputableMonolith.Ethics.Prefer M a₁ a₂ →
      IndisputableMonolith.Ethics.Prefer M b₁ b₂ →
      IndisputableMonolith.Ethics.Prefer M (C.comp a₁ b₁) (C.comp a₂ b₂)

def Symmetry : Prop :=
  ∀ {A : Type} (M : IndisputableMonolith.Ethics.CostModel A),
    (∀ a : A, IndisputableMonolith.Ethics.Prefer M a a) ∧
    (∀ {a b c : A},
      IndisputableMonolith.Ethics.Prefer M a b →
      IndisputableMonolith.Ethics.Prefer M b c →
      IndisputableMonolith.Ethics.Prefer M a c)

def Stability : Prop :=
  ∀ {A : Type} (M : IndisputableMonolith.Ethics.CostModel A)
    (C : IndisputableMonolith.Ethics.Composable M)
    {a b x : A},
      IndisputableMonolith.Ethics.Improves M a b →
      IndisputableMonolith.Ethics.Improves M (C.comp a x) (C.comp b x)

def All : Prop := Monotonicity ∧ Symmetry ∧ Stability

lemma monotonicity_holds : Monotonicity := by
  intro A M C a₁ a₂ b₁ b₂ ha hb
  exact IndisputableMonolith.Ethics.prefer_comp_mono M C ha hb

lemma symmetry_holds : Symmetry := by
  intro A M
  refine And.intro ?hRefl ?hTrans
  · intro a; exact IndisputableMonolith.Ethics.prefer_refl M a
  · intro a b c hab hbc; exact IndisputableMonolith.Ethics.prefer_trans M hab hbc

lemma stability_holds : Stability := by
  intro A M C a b x h
  exact IndisputableMonolith.Ethics.improves_comp_left M C h

lemma all_holds : All := And.intro monotonicity_holds (And.intro symmetry_holds stability_holds)

end Invariants
end Ethics
end IndisputableMonolith
