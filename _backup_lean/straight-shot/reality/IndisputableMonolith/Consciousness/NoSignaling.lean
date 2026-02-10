import Mathlib

/-!
# No‑Signaling (Mathematical Lemmas)

The repo's Θ layer talks about nonlocal correlations. To keep physics coherent,
we need a *no‑signaling* constraint: correlations must not enable controllable
faster‑than‑light communication.

This file is deliberately *math-first*:
- it defines a standard finite no‑signaling predicate for conditional tables
- it proves a basic theorem: any mixture of product response functions is no‑signaling

No empirical claims are made here.
-/

namespace IndisputableMonolith
namespace Consciousness
namespace NoSignaling

open scoped BigOperators

/-! ## Discrete conditional model (finite types) -/

abbrev Prob := ℝ

/-! A conditional table P(a,b | x,y) for finite outcome/input types. -/
structure CondTableData (X Y A B : Type) [Fintype X] [Fintype Y] [Fintype A] [Fintype B] where
  table : X → Y → A → B → Prob

variable {X Y A B L : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype L]

noncomputable def marginalA (P : CondTableData X Y A B) (x : X) (y : Y) (a : A) : Prob :=
  ∑ b : B, P.table x y a b

noncomputable def marginalB (P : CondTableData X Y A B) (x : X) (y : Y) (b : B) : Prob :=
  ∑ a : A, P.table x y a b

def NoSignalingA (P : CondTableData X Y A B) : Prop :=
  ∀ x : X, ∀ a : A, ∀ y1 y2 : Y, marginalA P x y1 a = marginalA P x y2 a

def NoSignalingB (P : CondTableData X Y A B) : Prop :=
  ∀ y : Y, ∀ b : B, ∀ x1 x2 : X, marginalB P x1 y b = marginalB P x2 y b

def NoSignalingProp (P : CondTableData X Y A B) : Prop :=
  NoSignalingA P ∧ NoSignalingB P

/-! ## Local hidden-variable form implies no-signaling -/

/-- Weight distribution over hidden variable L. -/
abbrev WeightFn (L : Type) := L → Prob

/-- Response function for Alice: P_A(a | l, x). -/
abbrev RespFnA (L X A : Type) := L → X → A → Prob

/-- Response function for Bob: P_B(b | l, y). -/
abbrev RespFnB (L Y B : Type) := L → Y → B → Prob

/-- LHV correlation: P(a,b|x,y) = Σ_l w(l) P_A(a|l,x) P_B(b|l,y). -/
noncomputable def LHVP (w : WeightFn L) (PA : RespFnA L X A) (PB : RespFnB L Y B) :
    CondTableData X Y A B :=
  ⟨fun x y a b => ∑ l : L, w l * PA l x a * PB l y b⟩

/-! ## Probability normalization assumptions -/

def IsProbDist {α : Type} [Fintype α] (p : α → Prob) : Prop :=
  (∀ a, 0 ≤ p a) ∧ (∑ a, p a = 1)

/-! ## Main theorem: LHV implies no-signaling

We use a hypothesis-style statement to make the types cleaner.
-/

/-- Auxiliary: marginalA of LHVP doesn't depend on y when PB is normalized. -/
lemma marginalA_LHVP_indep_y
    (w : WeightFn L) (PA : RespFnA L X A) (PB : RespFnB L Y B)
    (hPB : ∀ l : L, ∀ y : Y, ∑ b : B, PB l y b = 1)
    (x : X) (a : A) (y : Y) :
    marginalA (LHVP w PA PB) x y a = ∑ l : L, w l * PA l x a := by
  simp only [marginalA, LHVP]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hsumB : ∑ b : B, PB l y b = 1 := hPB l y
  have h1 : ∑ b : B, w l * PA l x a * PB l y b = w l * PA l x a * ∑ b : B, PB l y b := by
    rw [Finset.mul_sum]
  rw [h1, hsumB, mul_one]

/-- Auxiliary: marginalB of LHVP doesn't depend on x when PA is normalized. -/
lemma marginalB_LHVP_indep_x
    (w : WeightFn L) (PA : RespFnA L X A) (PB : RespFnB L Y B)
    (hPA : ∀ l : L, ∀ x : X, ∑ a : A, PA l x a = 1)
    (y : Y) (b : B) (x : X) :
    marginalB (LHVP w PA PB) x y b = ∑ l : L, w l * PB l y b := by
  simp only [marginalB, LHVP]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hsumA : ∑ a : A, PA l x a = 1 := hPA l x
  -- Use Finset.sum_congr to apply the algebraic rewrite pointwise
  have h0 : ∑ a : A, w l * PA l x a * PB l y b = ∑ a : A, w l * PB l y b * PA l x a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [h0]
  have h1 : ∑ a : A, w l * PB l y b * PA l x a = w l * PB l y b * ∑ a : A, PA l x a := by
    rw [Finset.mul_sum]
  rw [h1, hsumA, mul_one]

theorem noSignaling_of_LHV
    (w : WeightFn L) (PA : RespFnA L X A) (PB : RespFnB L Y B)
    (hPA : ∀ l : L, ∀ x : X, ∑ a : A, PA l x a = 1)
    (hPB : ∀ l : L, ∀ y : Y, ∑ b : B, PB l y b = 1) :
    NoSignalingProp (LHVP w PA PB) := by
  constructor
  · -- NoSignalingA
    intro x a y1 y2
    rw [marginalA_LHVP_indep_y w PA PB hPB x a y1,
        marginalA_LHVP_indep_y w PA PB hPB x a y2]
  · -- NoSignalingB
    intro y b x1 x2
    rw [marginalB_LHVP_indep_x w PA PB hPA y b x1,
        marginalB_LHVP_indep_x w PA PB hPA y b x2]

end NoSignaling
end Consciousness
end IndisputableMonolith
