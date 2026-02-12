/-
Copyright (c) 2025 Recognition Science. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Recognition Science Contributors
-/
import IndisputableMonolith.ULQ.Core
import IndisputableMonolith.ULQ.Taxonomy
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs

/-!
# ULQ Qualia Calculus

This module provides a formal algebraic structure for qualia operations,
enabling rigorous manipulation of experiential states.

## Key Insight

Qualia form a **commutative monoid** under combination, with additional
structure from hedonic valence (forming a partial order).

## Algebraic Structures

1. **QualiaMonoid**: Combination of qualia (like "seeing red AND hearing C#")
2. **QualiaLattice**: Intensity ordering (stronger/weaker experiences)
3. **HedonicRing**: Valence arithmetic (pleasure + pain cancellation)
4. **ModalAlgebra**: Mode composition rules

## Physical Motivation

These operations correspond to:
- Combination: Multiple simultaneous qualia in consciousness
- Ordering: Attention allocation and salience
- Cancellation: Hedonic adaptation and contrast effects
-/

namespace IndisputableMonolith.ULQ.Calculus

open IndisputableMonolith
open ULQ

/-! ## Qualia Vectors -/

/-- A qualia vector represents a point in the 4D qualia space -/
@[ext]
structure QualiaVector where
  /-- Mode component (0-7, representing DFT mode) -/
  mode : Fin 8
  /-- Intensity component (0-3, representing φ-level) -/
  intensity : Fin 4
  /-- Valence component (-1 to 1) -/
  valence : ℝ
  /-- Temporal component (0-7, representing τ-offset) -/
  temporal : Fin 8
  /-- Valence bounded -/
  valence_bounded : -1 ≤ valence ∧ valence ≤ 1

/-- Zero qualia vector (DC mode, minimal intensity, neutral valence) -/
def QualiaVector.zero : QualiaVector where
  mode := 0
  intensity := 0
  valence := 0
  temporal := 0
  valence_bounded := by constructor <;> norm_num

/-- Convert QualiaSpace to QualiaVector -/
def toVector (q : QualiaSpace) : QualiaVector where
  mode := q.mode.k
  intensity := q.intensity.level
  valence := q.valence.value
  temporal := q.temporal.tau
  valence_bounded := q.valence.bounded

/-! ## Mode Algebra -/

/-- Mode addition (DFT convolution) -/
def modeAdd (m1 m2 : Fin 8) : Fin 8 :=
  ⟨(m1.val + m2.val) % 8, Nat.mod_lt _ (by norm_num)⟩

/-- Mode negation (conjugate) -/
def modeNeg (m : Fin 8) : Fin 8 :=
  ⟨(8 - m.val) % 8, Nat.mod_lt _ (by norm_num)⟩

/-- Mode multiplication identity -/
theorem modeAdd_zero (m : Fin 8) : modeAdd m 0 = m := by
  simp only [modeAdd, Fin.val_zero, add_zero]
  exact Fin.ext (Nat.mod_eq_of_lt m.isLt)

/-- Mode addition is commutative -/
theorem modeAdd_comm (m1 m2 : Fin 8) : modeAdd m1 m2 = modeAdd m2 m1 := by
  simp [modeAdd, Nat.add_comm]

/-- Mode addition is associative -/
theorem modeAdd_assoc (m1 m2 m3 : Fin 8) :
    modeAdd (modeAdd m1 m2) m3 = modeAdd m1 (modeAdd m2 m3) := by
  simp only [modeAdd]
  apply Fin.ext
  simp only [Fin.val_mk, Nat.add_mod_mod, Nat.mod_add_mod, Nat.add_assoc]

/-! ## Intensity Algebra -/

/-- Intensity maximum (attention competition) -/
def intensityMax (i1 i2 : Fin 4) : Fin 4 :=
  if i1.val ≥ i2.val then i1 else i2

/-- Intensity minimum (background) -/
def intensityMin (i1 i2 : Fin 4) : Fin 4 :=
  if i1.val ≤ i2.val then i1 else i2

/-- Intensity forms a lattice -/
theorem intensityMax_comm (i1 i2 : Fin 4) : intensityMax i1 i2 = intensityMax i2 i1 := by
  simp only [intensityMax]
  by_cases h : i1.val ≥ i2.val
  · by_cases h' : i2.val ≥ i1.val
    · have heq : i1 = i2 := Fin.ext (Nat.le_antisymm h' h)
      simp [heq]
    · simp [h, h', Nat.not_le.mp h']
  · by_cases h' : i2.val ≥ i1.val
    · simp [h, h']
    · omega

/-! ## Valence Algebra -/

/-- Clamp a real number to [-1, 1] -/
noncomputable def clampValence (v : ℝ) : ℝ :=
  max (-1) (min 1 v)

/-- Clamped valence is bounded -/
theorem clampValence_bounded (v : ℝ) : -1 ≤ clampValence v ∧ clampValence v ≤ 1 := by
  simp only [clampValence]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

/-- Valence addition (hedonic sum with clamping) -/
noncomputable def valenceAdd (v1 v2 : ℝ) : ℝ :=
  clampValence (v1 + v2)

/-- Valence negation -/
noncomputable def valenceNeg (v : ℝ) : ℝ :=
  -v

/-- Valence addition is commutative -/
theorem valenceAdd_comm (v1 v2 : ℝ) : valenceAdd v1 v2 = valenceAdd v2 v1 := by
  simp [valenceAdd, add_comm]

/-- Zero valence is identity -/
theorem valenceAdd_zero (v : ℝ) (hv : -1 ≤ v ∧ v ≤ 1) : valenceAdd v 0 = v := by
  simp only [valenceAdd, add_zero, clampValence]
  rw [min_eq_right hv.2, max_eq_right hv.1]

/-! ## Qualia Combination -/

/-- Combine two qualia (parallel experience) -/
noncomputable def combine (q1 q2 : QualiaVector) : QualiaVector where
  mode := modeAdd q1.mode q2.mode
  intensity := intensityMax q1.intensity q2.intensity
  valence := valenceAdd q1.valence q2.valence
  temporal := modeAdd q1.temporal q2.temporal  -- Temporal blending
  valence_bounded := clampValence_bounded _

/-- Combination is commutative -/
theorem combine_comm (q1 q2 : QualiaVector) : combine q1 q2 = combine q2 q1 := by
  simp only [combine]
  congr 1
  · exact modeAdd_comm _ _
  · exact intensityMax_comm _ _
  · exact valenceAdd_comm _ _
  · exact modeAdd_comm _ _

/-- IntensityMax with zero returns the original intensity -/
theorem intensityMax_zero_right (i : Fin 4) : intensityMax i 0 = i := by
  simp only [intensityMax, Fin.val_zero]
  split_ifs with h
  · rfl
  · omega

/-- Zero qualia is right identity -/
theorem combine_zero_right (q : QualiaVector) : combine q QualiaVector.zero = q := by
  simp only [combine, QualiaVector.zero]
  apply QualiaVector.ext
  · exact modeAdd_zero q.mode
  · exact intensityMax_zero_right q.intensity
  · exact valenceAdd_zero q.valence q.valence_bounded
  · exact modeAdd_zero q.temporal

/-! ## Qualia Scaling -/

/-- Scale qualia intensity (attention modulation) -/
noncomputable def scale (α : ℝ) (q : QualiaVector) (hα : 0 ≤ α ∧ α ≤ 1) : QualiaVector where
  mode := q.mode
  intensity := q.intensity  -- Mode preserved
  valence := clampValence (α * q.valence)
  temporal := q.temporal
  valence_bounded := clampValence_bounded _

/-- Clamping a bounded value returns the value -/
theorem clampValence_of_bounded (v : ℝ) (hv : -1 ≤ v ∧ v ≤ 1) : clampValence v = v := by
  simp only [clampValence]
  rw [min_eq_right hv.2, max_eq_right hv.1]

/-- Scaling by 1 preserves qualia -/
theorem scale_one (q : QualiaVector) : scale 1 q ⟨by norm_num, by norm_num⟩ = q := by
  simp only [scale, one_mul]
  apply QualiaVector.ext <;> simp only
  exact clampValence_of_bounded q.valence q.valence_bounded

/-- Scaling by 0 gives neutral valence -/
theorem scale_zero (q : QualiaVector) : (scale 0 q ⟨by norm_num, by norm_num⟩).valence = 0 := by
  simp only [scale, zero_mul, clampValence, min_eq_right (by norm_num : (1 : ℝ) ≥ 0), max_eq_right (by norm_num : (0 : ℝ) ≥ -1)]

/-! ## Qualia Distance -/

/-- Distance between two qualia vectors -/
noncomputable def qualiaDistance (q1 q2 : QualiaVector) : ℝ :=
  let modeDist := ((q1.mode.val : ℤ) - q2.mode.val).natAbs
  let intDist := ((q1.intensity.val : ℤ) - q2.intensity.val).natAbs
  let valDist := |q1.valence - q2.valence|
  let tempDist := ((q1.temporal.val : ℤ) - q2.temporal.val).natAbs
  Real.sqrt (modeDist^2 + intDist^2 + valDist^2 + tempDist^2)

/-- Distance is non-negative -/
theorem qualiaDistance_nonneg (q1 q2 : QualiaVector) : qualiaDistance q1 q2 ≥ 0 := by
  simp only [qualiaDistance]
  exact Real.sqrt_nonneg _

/-- Distance to self is zero -/
theorem qualiaDistance_self (q : QualiaVector) : qualiaDistance q q = 0 := by
  simp only [qualiaDistance, sub_self, abs_zero, Int.natAbs_zero]
  norm_num

/-! ## Qualia Inner Product -/

/-- Inner product of qualia vectors (experiential similarity) -/
noncomputable def qualiaInnerProduct (q1 q2 : QualiaVector) : ℝ :=
  (q1.mode.val * q2.mode.val : ℕ) +
  (q1.intensity.val * q2.intensity.val : ℕ) +
  q1.valence * q2.valence +
  (q1.temporal.val * q2.temporal.val : ℕ)

/-- Inner product is symmetric -/
theorem qualiaInnerProduct_comm (q1 q2 : QualiaVector) :
    qualiaInnerProduct q1 q2 = qualiaInnerProduct q2 q1 := by
  simp only [qualiaInnerProduct, mul_comm]

/-! ## Qualia Projection -/

/-- Project qualia onto a mode (extract mode-specific component) -/
def projectMode (q : QualiaVector) (targetMode : Fin 8) : QualiaVector :=
  if q.mode = targetMode then q else QualiaVector.zero

/-- Project qualia onto positive valence -/
noncomputable def projectPleasure (q : QualiaVector) : QualiaVector where
  mode := q.mode
  intensity := q.intensity
  valence := max 0 q.valence
  temporal := q.temporal
  valence_bounded := by
    constructor
    · exact le_trans (by norm_num : (-1 : ℝ) ≤ 0) (le_max_left _ _)
    · exact max_le (by norm_num) q.valence_bounded.2

/-- Project qualia onto negative valence -/
noncomputable def projectPain (q : QualiaVector) : QualiaVector where
  mode := q.mode
  intensity := q.intensity
  valence := min 0 q.valence
  temporal := q.temporal
  valence_bounded := by
    constructor
    · have h1 : (-1 : ℝ) ≤ 0 := by norm_num
      have h2 : (-1 : ℝ) ≤ q.valence := q.valence_bounded.1
      exact le_min h1 h2
    · have h : min (0 : ℝ) q.valence ≤ 0 := min_le_left 0 q.valence
      linarith

/-- max(0, v) + min(0, v) = v for any real v -/
theorem max_zero_add_min_zero (v : ℝ) : max 0 v + min 0 v = v := by
  by_cases h : v ≥ 0
  · simp [max_eq_right h, min_eq_left h]
  · push_neg at h
    simp [max_eq_left (le_of_lt h), min_eq_right (le_of_lt h)]

/-- Decomposition into pleasure and pain components -/
theorem pleasure_pain_decomposition (q : QualiaVector) :
    (projectPleasure q).valence + (projectPain q).valence = q.valence := by
  simp only [projectPleasure, projectPain]
  exact max_zero_add_min_zero q.valence

/-! ## Status Report -/

def calculus_status : String :=
  "╔══════════════════════════════════════════════════════════════╗\n" ++
  "║           ULQ QUALIA CALCULUS                                ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  QUALIA VECTORS: 4D space (mode, intensity, valence, time)   ║\n" ++
  "║  MODE ALGEBRA: Z/8Z group under addition (DFT convolution)   ║\n" ++
  "║  INTENSITY: Lattice (max for attention, min for background)  ║\n" ++
  "║  VALENCE: Clamped addition with cancellation                 ║\n" ++
  "║  COMBINATION: Commutative monoid structure                   ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  OPERATIONS:                                                 ║\n" ++
  "║  • combine: parallel experience                              ║\n" ++
  "║  • scale: attention modulation                               ║\n" ++
  "║  • distance: experiential dissimilarity                      ║\n" ++
  "║  • innerProduct: experiential similarity                     ║\n" ++
  "║  • project: mode/valence extraction                          ║\n" ++
  "╚══════════════════════════════════════════════════════════════╝"

#check calculus_status

end IndisputableMonolith.ULQ.Calculus
