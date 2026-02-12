import Mathlib

namespace IndisputableMonolith
namespace Ethics

noncomputable section
open Classical

universe u

/-- A minimal cost model over actions of type `A`. Costs are nonnegative reals. -/
structure CostModel (A : Type u) where
  cost : A → ℝ
  nonneg : ∀ a, 0 ≤ cost a

variable {A : Type u}

/-- Ethical preference: `a ≼ b` iff `cost a ≤ cost b` (lower cost is better). -/
def Prefer (M : CostModel A) (a b : A) : Prop := M.cost a ≤ M.cost b

infix:50 "≼" => Prefer

/-- Net improvement predicate: `a` strictly improves on `b`. -/
def Improves (M : CostModel A) (a b : A) : Prop := M.cost a < M.cost b

/-- Reflexivity: every action is at least as good as itself. -/
lemma prefer_refl (M : CostModel A) (a : A) : Prefer M a a := by
  dsimp [Prefer]
  exact le_rfl

/-- Transitivity: if `a ≼ b` and `b ≼ c`, then `a ≼ c`. -/
lemma prefer_trans (M : CostModel A) {a b c : A}
  (hab : Prefer M a b) (hbc : Prefer M b c) : Prefer M a c := by
  dsimp [Prefer] at hab hbc ⊢; exact le_trans hab hbc

/-- Preorder instance for preference. -/
instance (M : CostModel A) : Preorder A where
  le := fun a b => Prefer M a b
  le_refl := fun a => prefer_refl M a
  le_trans := fun a b c hab hbc => prefer_trans M hab hbc

/-- Composable actions under a cost model: binary composition with subadditivity and monotonicity. -/
structure Composable (M : CostModel A) where
  comp : A → A → A
  subadd : ∀ a b, M.cost (comp a b) ≤ M.cost a + M.cost b
  mono : ∀ a a' b b', Prefer M a a' → Prefer M b b' → Prefer M (comp a b) (comp a' b')
  strict_mono_left : ∀ a a' x, Improves M a a' → Improves M (comp a x) (comp a' x)

/-- Monotonicity of composition w.r.t. preference. -/
theorem prefer_comp_mono (M : CostModel A) (C : Composable M)
  {a₁ a₂ b₁ b₂ : A}
  (ha : Prefer M a₁ a₂) (hb : Prefer M b₁ b₂) :
  Prefer M (C.comp a₁ b₁) (C.comp a₂ b₂) := by
  dsimp [Prefer] at ha hb ⊢
  exact C.mono a₁ a₂ b₁ b₂ ha hb

/-- Composition preserves improvement. -/
theorem improves_comp_left (M : CostModel A) (C : Composable M)
  {a b x : A} (h : Improves M a b) : Improves M (C.comp a x) (C.comp b x) := by
  exact C.strict_mono_left a b x h

/- Placeholder for Measurement.CQ dependency -/
variable {CQ : Type u}

/-- CQ alignment at threshold θ ∈ [0,1]: score ≥ θ. -/
def CQAligned (score : CQ → ℝ) (θ : ℝ) (c : CQ) : Prop :=
  0 ≤ θ ∧ θ ≤ 1 ∧ score c ≥ θ

/-- Ethical admissibility under 45‑gap: either no experience required, or the plan includes experience. -/
/- Placeholder for Gap45 dependency -/
def Admissible (requiresExperience : CQ → Nat → Prop) (period : Nat) (c : CQ) (hasExperience : Prop) : Prop :=
  ¬ requiresExperience c period ∨ hasExperience

/-- Prefer alignment: higher CQ never hurts in the costless tie (axiom placeholder to be specialized).
    Prefer higher CQ does not break ties: if costs are equal and `c₁` is at least as aligned as `c₂`,
    then `a` is preferred to `b`. -/
theorem prefer_by_cq (M : CostModel A) (a b : A) (c₁ c₂ : CQ) (θ : ℝ)
  (score : CQ → ℝ)
  (_ : 0 ≤ θ ∧ θ ≤ 1) (_ : CQAligned score θ c₂ → CQAligned score θ c₁)
  (hcost : M.cost a = M.cost b) : Prefer M a b := by
  dsimp [Prefer]
  simp [hcost]

/-- Lexicographic ethical preference with admissibility first, then cost preference. -/
def PreferLex (M : CostModel A) (requiresExperience : CQ → Nat → Prop) (period : Nat) (cq : CQ)
  (hasExpA hasExpB : Prop) (a b : A) : Prop :=
  (Admissible requiresExperience period cq hasExpA ∧ ¬ Admissible requiresExperience period cq hasExpB)
  ∨ (Admissible requiresExperience period cq hasExpA ∧ Admissible requiresExperience period cq hasExpB ∧ Prefer M a b)

end

end Ethics
end IndisputableMonolith
