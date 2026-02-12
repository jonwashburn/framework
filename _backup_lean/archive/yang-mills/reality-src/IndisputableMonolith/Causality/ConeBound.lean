import Mathlib

namespace IndisputableMonolith
namespace Causality

/-! Minimal ConeBound: local definitions to avoid heavy imports. Provides
    ball growth bounds under a bounded-degree step relation. -/

class BoundedStep (α : Type) (degree_bound : outParam Nat) where
  step : α → α → Prop
  neighbors : α → Finset α
  step_iff_mem : ∀ x y, step x y ↔ y ∈ neighbors x
  degree_bound_holds : ∀ x, (neighbors x).card ≤ degree_bound

structure Kinematics (α : Type) where
  step : α → α → Prop

def ballP (K : Kinematics α) (x : α) : Nat → α → Prop
| 0, y => y = x
| Nat.succ n, y => ballP K x n y ∨ ∃ z, ballP K x n z ∧ K.step z y

namespace ConeBound

variable {α : Type} {d : Nat}
variable [DecidableEq α]
variable [B : BoundedStep α d]

def KB : Kinematics α := { step := B.step }

noncomputable def ballFS (x : α) : Nat → Finset α
| 0 => {x}
| Nat.succ n =>
    let prev := ballFS x n
    prev ∪ prev.biUnion (fun z => B.neighbors z)

theorem mem_ballFS_iff_ballP (x y : α) : ∀ n, y ∈ ballFS (α:=α) x n ↔ ballP (KB (α:=α)) x n y := by
  intro n
  induction n with
  | zero =>
    dsimp [ballFS, ballP]
    constructor
    · intro hy; simpa using hy
    · intro hy; simpa using hy
  | succ n ih =>
    dsimp [ballFS, ballP]
    constructor
    · intro hy
      have : y ∈ ballFS (α:=α) x n ∨ y ∈ (ballFS (α:=α) x n).biUnion (fun z => B.neighbors z) := by
        simpa using Finset.mem_union.mp hy
      cases this with
      | inl hy_prev => exact Or.inl (by simpa using (ih.mp hy_prev))
      | inr hy_union =>
        rcases Finset.mem_biUnion.mp hy_union with ⟨z, hz, hyz⟩
        refine Or.inr ?_;
        refine ⟨z, ?_, ?_⟩
        · exact (ih.mp hz)
        · simpa [KB]
    · intro hy
      cases hy with
      | inl hy0 =>
        have : y ∈ ballFS (α:=α) x n := by simpa using (ih.mpr hy0)
        exact by
          have := Finset.mem_union.mpr (Or.inl this)
          simpa
      | inr hy1 =>
        rcases hy1 with ⟨z, hz, hstep⟩
        have hz' : z ∈ ballFS (α:=α) x n := by simpa using (ih.mpr hz)
        have hy_union : y ∈ (ballFS (α:=α) x n).biUnion (fun z => B.neighbors z) := by
          exact Finset.mem_biUnion.mpr ⟨z, hz', by simpa [KB] using hstep⟩
        exact by
          have := Finset.mem_union.mpr (Or.inr hy_union)
          simpa
theorem card_singleton {x : α} : ({x} : Finset α).card = 1 :=
  Finset.card_singleton x
theorem card_union_le (s t : Finset α) : (s ∪ t).card ≤ s.card + t.card :=
  Finset.card_union_le s t
theorem card_bind_le_sum (s : Finset α) (f : α → Finset α) :
  (s.biUnion f).card ≤ Finset.sum s (fun z => (f z).card) :=
  Finset.card_biUnion_le_sum s f
theorem sum_card_neighbors_le (s : Finset α) :
  Finset.sum s (fun z => (B.neighbors z).card) ≤ d * s.card := by
  apply Finset.sum_le_sum
  intro z hz
  exact B.degree_bound_holds z
theorem card_bind_neighbors_le (s : Finset α) :
  (s.biUnion (fun z => B.neighbors z)).card ≤ d * s.card := by
  have h1 := card_bind_le_sum s (fun z => B.neighbors z)
  have h2 := sum_card_neighbors_le s
  exact Nat.le_trans h1 h2
theorem card_ballFS_succ_le (x : α) (n : Nat) :
  (ballFS (α:=α) x (n+1)).card ≤ (1 + d) * (ballFS (α:=α) x n).card := by
  dsimp [ballFS]
  let prev := ballFS (α:=α) x n
  let new_neighbors := prev.biUnion (fun z => B.neighbors z)
  have h_union := card_union_le prev new_neighbors
  have h_neighbors := card_bind_neighbors_le prev
  have h_combined := Nat.le_trans h_union (Nat.add_le_add_left h_neighbors prev.card)
  rw [Nat.mul_add, Nat.mul_one] at h_combined
  exact h_combined
theorem ballFS_card_le_geom (x : α) : ∀ n : Nat, (ballFS (α:=α) x n).card ≤ (1 + d) ^ n := by
  intro n
  induction n with
  | zero =>
    dsimp [ballFS]
    rw [card_singleton]
    rw [Nat.pow_zero]
    exact Nat.le_refl 1
  | succ n ih =>
    have h_succ := card_ballFS_succ_le x n
    have h_pow := Nat.pow_succ (1 + d) n
    rw [h_pow] at h_succ
    exact Nat.le_trans h_succ (Nat.mul_le_mul_left (1 + d) ih)

end ConeBound
end Causality
end IndisputableMonolith
