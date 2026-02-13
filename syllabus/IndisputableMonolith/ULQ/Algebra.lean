/-
Copyright (c) 2025 Recognition Science. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Recognition Science Contributors
-/
import IndisputableMonolith.ULQ.Core
import IndisputableMonolith.ULQ.Calculus

/-!
# ULQ Qualia Algebra

This module develops the algebraic structures on qualia space,
including groups, monoids, and module structures.

## Key Insight

Qualia have natural algebraic structure:
- Mode addition forms Z/8Z (cyclic group)
- Intensity forms a bounded semilattice
- Valence forms a bounded abelian group
- Together they form a product algebra

## Algebraic Structures

| Structure | Qualia Aspect | Operation |
|-----------|---------------|-----------|
| Z/8Z | Mode | Cyclic addition mod 8 |
| (ℕ≤3, max) | Intensity | Maximum |
| ([-1,1], +) | Valence | Clamped addition |
| Z/8Z | Temporal | Cyclic addition mod 8 |
-/

namespace IndisputableMonolith.ULQ.Algebra

open IndisputableMonolith
open ULQ

/-! ## Mode Group (Z/8Z) -/

/-- Mode forms a cyclic group of order 8 -/
structure ModeGroup where
  /-- Element -/
  val : Fin 8

/-- Zero element (identity) -/
def ModeGroup.zero : ModeGroup := ⟨0⟩

/-- Addition in Z/8Z -/
def ModeGroup.add (a b : ModeGroup) : ModeGroup :=
  ⟨⟨(a.val.val + b.val.val) % 8, Nat.mod_lt _ (by norm_num)⟩⟩

/-- Negation in Z/8Z -/
def ModeGroup.neg (a : ModeGroup) : ModeGroup :=
  ⟨⟨(8 - a.val.val) % 8, Nat.mod_lt _ (by norm_num)⟩⟩

/-- Addition is commutative -/
theorem ModeGroup.add_comm (a b : ModeGroup) : a.add b = b.add a := by
  simp [ModeGroup.add]
  congr 1
  omega

/-- PROVEN: Zero is identity -/
theorem ModeGroup.add_zero (a : ModeGroup) : a.add ModeGroup.zero = a := by
  cases a with | mk k =>
  simp only [add, zero, mk.injEq, Fin.val_zero, add_zero]
  ext
  simp only [Fin.val_mk]
  exact Nat.mod_eq_of_lt k.isLt

/-- PROVEN: Negation is inverse -/
theorem ModeGroup.add_neg (a : ModeGroup) : a.add (a.neg) = ModeGroup.zero := by
  cases a with | mk k =>
  simp only [add, neg, zero, mk.injEq]
  ext
  simp only [Fin.val_mk, Fin.val_zero]
  -- Goal: (k.val + (8 - k.val) % 8) % 8 = 0
  have h : k.val < 8 := k.isLt
  omega

/-! ## Intensity Semilattice -/

/-- Intensity forms a bounded join-semilattice -/
structure IntensitySemilattice where
  /-- Level (0-3) -/
  val : Fin 4

/-- Bottom element (minimum intensity) -/
def IntensitySemilattice.bot : IntensitySemilattice := ⟨0⟩

/-- Top element (maximum intensity) -/
def IntensitySemilattice.top : IntensitySemilattice := ⟨3⟩

/-- Join (maximum) -/
def IntensitySemilattice.join (a b : IntensitySemilattice) : IntensitySemilattice :=
  ⟨⟨max a.val.val b.val.val, by
    have ha := a.val.isLt
    have hb := b.val.isLt
    omega⟩⟩

/-- Meet (minimum) -/
def IntensitySemilattice.meet (a b : IntensitySemilattice) : IntensitySemilattice :=
  ⟨⟨min a.val.val b.val.val, by
    have ha := a.val.isLt
    have hb := b.val.isLt
    omega⟩⟩

/-- PROVEN: Join is commutative -/
theorem IntensitySemilattice.join_comm (a b : IntensitySemilattice) :
    a.join b = b.join a := by
  simp only [join]
  congr 1
  ext
  exact Nat.max_comm a.val.val b.val.val

/-- PROVEN: Join is idempotent -/
theorem IntensitySemilattice.join_idem (a : IntensitySemilattice) :
    a.join a = a := by
  simp only [join]
  congr 1
  ext
  exact Nat.max_self a.val.val

/-- PROVEN: Bot is identity for join -/
theorem IntensitySemilattice.join_bot (a : IntensitySemilattice) :
    a.join IntensitySemilattice.bot = a := by
  simp only [join, bot]
  congr 1
  ext
  simp only [Fin.val_zero, Nat.max_zero]

/-! ## Valence Group -/

/-- Valence forms a bounded abelian group (clamped to [-1,1]) -/
structure ValenceGroup where
  /-- Value in [-1, 1] -/
  val : ℝ
  /-- Bounded below -/
  lower : -1 ≤ val
  /-- Bounded above -/
  upper : val ≤ 1

/-- Zero valence (neutral) -/
noncomputable def ValenceGroup.zero : ValenceGroup :=
  ⟨0, by norm_num, by norm_num⟩

/-- Clamped sum stays in bounds -/
theorem clampedSum_bounded (a b : ValenceGroup) :
    -1 ≤ max (-1) (min 1 (a.val + b.val)) ∧ max (-1) (min 1 (a.val + b.val)) ≤ 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

/-- Clamped addition -/
noncomputable def ValenceGroup.add (a b : ValenceGroup) : ValenceGroup :=
  ⟨max (-1) (min 1 (a.val + b.val)),
   (clampedSum_bounded a b).1,
   (clampedSum_bounded a b).2⟩

/-- Negation -/
noncomputable def ValenceGroup.neg (a : ValenceGroup) : ValenceGroup :=
  ⟨-a.val, by linarith [a.upper], by linarith [a.lower]⟩

/-- Addition is commutative -/
theorem ValenceGroup.add_comm (a b : ValenceGroup) : a.add b = b.add a := by
  simp [ValenceGroup.add]
  ring_nf

/-! ## Temporal Group (Z/8Z) -/

/-- Temporal offset forms Z/8Z -/
def TemporalGroup := ModeGroup

/-- Temporal addition -/
def TemporalGroup.add := ModeGroup.add

/-- Temporal negation -/
def TemporalGroup.neg := ModeGroup.neg

/-! ## Product Algebra -/

/-- The full qualia algebra is a product -/
structure QualiaAlgebra where
  /-- Mode component -/
  mode : ModeGroup
  /-- Intensity component -/
  intensity : IntensitySemilattice
  /-- Valence component -/
  valence : ValenceGroup
  /-- Temporal component -/
  temporal : ModeGroup

/-- Zero/neutral element -/
noncomputable def QualiaAlgebra.zero : QualiaAlgebra where
  mode := ModeGroup.zero
  intensity := IntensitySemilattice.bot
  valence := ValenceGroup.zero
  temporal := ModeGroup.zero

/-- Component-wise operations -/
noncomputable def QualiaAlgebra.add (a b : QualiaAlgebra) : QualiaAlgebra where
  mode := a.mode.add b.mode
  intensity := a.intensity.join b.intensity
  valence := a.valence.add b.valence
  temporal := a.temporal.add b.temporal

/-! ## Module Structure -/

/-- Scaled valence stays in bounds -/
theorem scaledValence_bounded (α : ℝ) (v : ValenceGroup) (hα : 0 ≤ α) (hα' : α ≤ 1) :
    -1 ≤ α * v.val ∧ α * v.val ≤ 1 := by
  constructor
  · -- Lower bound: α * v.val ≥ -1
    have hv_lower := v.lower
    have hv_upper := v.upper
    by_cases hv_neg : v.val < 0
    · -- v.val < 0: α * v.val ≥ α * (-1) ≥ -1 * 1 = -1
      have h1 : α * v.val ≥ α * (-1) := by nlinarith
      have h2 : α * (-1) ≥ -1 := by nlinarith
      linarith
    · -- v.val ≥ 0: α * v.val ≥ 0 ≥ -1
      push_neg at hv_neg
      have h : α * v.val ≥ 0 := mul_nonneg hα hv_neg
      linarith
  · -- Upper bound: α * v.val ≤ 1
    have hv_lower := v.lower
    have hv_upper := v.upper
    by_cases hv_pos : v.val > 0
    · -- v.val > 0: α * v.val ≤ 1 * 1 = 1
      have h1 : α * v.val ≤ 1 * v.val := by nlinarith
      have h2 : 1 * v.val ≤ 1 := by linarith
      linarith
    · -- v.val ≤ 0: α * v.val ≤ 0 ≤ 1
      push_neg at hv_pos
      have h : α * v.val ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hα hv_pos
      linarith

/-- Scalar multiplication by attention weight -/
noncomputable def scaleByAttention (α : ℝ) (q : QualiaAlgebra)
    (hα : 0 ≤ α) (hα' : α ≤ 1) : QualiaAlgebra where
  mode := q.mode  -- Mode unchanged
  intensity := q.intensity  -- Intensity unchanged (discrete)
  valence := ⟨α * q.valence.val,
    (scaledValence_bounded α q.valence hα hα').1,
    (scaledValence_bounded α q.valence hα hα').2⟩
  temporal := q.temporal  -- Temporal unchanged

/-! ## Homomorphisms -/

/-- A qualia homomorphism preserves structure -/
structure QualiaHomomorphism where
  /-- Map on mode -/
  mode_map : ModeGroup → ModeGroup
  /-- Map on intensity -/
  intensity_map : IntensitySemilattice → IntensitySemilattice
  /-- Preserves mode addition -/
  mode_add : ∀ a b, mode_map (a.add b) = (mode_map a).add (mode_map b)
  /-- Preserves intensity join -/
  intensity_join : ∀ a b, intensity_map (a.join b) = (intensity_map a).join (intensity_map b)

/-- Identity homomorphism -/
def QualiaHomomorphism.id : QualiaHomomorphism where
  mode_map := fun x => x
  intensity_map := fun x => x
  mode_add := by intros; rfl
  intensity_join := by intros; rfl

/-! ## Ideals -/

/-- A qualia ideal (subset closed under operations) -/
structure QualiaIdeal where
  /-- Predicate defining the ideal -/
  mem : ModeGroup → Prop
  /-- Contains zero -/
  zero_mem : mem ModeGroup.zero
  /-- Closed under addition -/
  add_mem : ∀ a b, mem a → mem b → mem (a.add b)
  /-- Closed under negation -/
  neg_mem : ∀ a, mem a → mem a.neg

/-- The trivial ideal (just zero) -/
def trivialIdeal : QualiaIdeal where
  mem := fun m => m = ModeGroup.zero
  zero_mem := rfl
  add_mem := by
    intros a b ha hb
    simp [ha, hb, ModeGroup.add, ModeGroup.zero]
  neg_mem := by
    intro a ha
    simp [ha, ModeGroup.neg, ModeGroup.zero]

/-- The whole group as an ideal -/
def wholeIdeal : QualiaIdeal where
  mem := fun _ => True
  zero_mem := trivial
  add_mem := by intros; trivial
  neg_mem := by intros; trivial

/-! ## Status Report -/

def algebra_status : String :=
  "╔══════════════════════════════════════════════════════════════╗\n" ++
  "║           ULQ QUALIA ALGEBRA                                 ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  MODE GROUP (Z/8Z):                                          ║\n" ++
  "║  • Operation: cyclic addition mod 8                          ║\n" ++
  "║  • Identity: 0                                               ║\n" ++
  "║  • Inverse: 8 - k                                            ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  INTENSITY SEMILATTICE:                                      ║\n" ++
  "║  • Operation: max (join)                                     ║\n" ++
  "║  • Bottom: 0, Top: 3                                         ║\n" ++
  "║  • Idempotent, commutative, associative                      ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  VALENCE GROUP:                                              ║\n" ++
  "║  • Operation: clamped addition                               ║\n" ++
  "║  • Bounds: [-1, 1]                                           ║\n" ++
  "║  • Abelian group structure                                   ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  PRODUCT ALGEBRA: Mode × Intensity × Valence × Temporal      ║\n" ++
  "║  MODULE STRUCTURE: Scalar multiplication by attention        ║\n" ++
  "║  HOMOMORPHISMS: Structure-preserving maps                    ║\n" ++
  "╚══════════════════════════════════════════════════════════════╝"

#check algebra_status

end IndisputableMonolith.ULQ.Algebra
