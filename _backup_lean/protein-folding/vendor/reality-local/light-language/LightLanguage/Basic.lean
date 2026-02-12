/-
  Light Language: Basic Definitions

  Foundational types and properties for consciousness-level recognition operators.

  This module provides:
  - Eight-tick window representation
  - Neutrality (sum = 0) definition
  - Vector operations on windows
  - Basic lemmas about neutral subspaces

  Based on Recognition Science eight-tick theorem (T6):
    Minimal period 2^D (D=3 ⇒ 8) for ledger-compatible walk on Q₃ hypercube.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Instances.Real

namespace LightLanguage

/-- Eight-tick window: fundamental temporal unit from RS theorem T6 -/
def EightTick := Fin 8

/-- A window is an 8-dimensional real vector representing one recognition cycle -/
def Window := EightTick → ℝ

/-- The constant vector (all ones) -/
def ones : Window := fun _ => 1

/-- Sum of elements in a window -/
def windowSum (w : Window) : ℝ :=
  ∑ i : EightTick, w i

/-- A window is neutral if its sum equals zero -/
def IsNeutral (w : Window) : Prop :=
  windowSum w = 0

/-- The neutral subspace: all windows with sum = 0 -/
def NeutralSubspace : Set Window :=
  {w | IsNeutral w}

/-- Batch of windows: n × 8 matrix -/
def WindowBatch (n : ℕ) := Fin n → Window

/-- All windows in a batch are neutral -/
def BatchIsNeutral {n : ℕ} (batch : WindowBatch n) : Prop :=
  ∀ i : Fin n, IsNeutral (batch i)

/-- Linear operator on windows (8×8 matrix) -/
def WindowOperator := Window → Window

/-- An operator preserves neutrality if it maps neutral windows to neutral windows -/
def PreservesNeutrality (op : WindowOperator) : Prop :=
  ∀ w : Window, IsNeutral w → IsNeutral (op w)

/-- Matrix representation of a window operator -/
def OperatorMatrix := Matrix EightTick EightTick ℝ

/-- Apply matrix to window (standard matrix-vector multiplication) -/
def applyMatrix (M : OperatorMatrix) (w : Window) : Window :=
  fun i => ∑ j : EightTick, M i j * w j

/-- Column sum of a matrix -/
def columnSum (M : OperatorMatrix) (j : EightTick) : ℝ :=
  ∑ i : EightTick, M i j

/-- All column sums equal 1 (neutrality preservation condition) -/
def AllColumnSumsOne (M : OperatorMatrix) : Prop :=
  ∀ j : EightTick, columnSum M j = 1

/-! ## Basic Lemmas -/

/-- The ones vector has sum 8 -/
lemma ones_sum : windowSum ones = 8 := by
  unfold windowSum ones
  -- ∑ i : Fin 8, 1 = 8
  have : ∑ i : EightTick, (1 : ℝ) = (Finset.univ.card : ℝ) := by
    exact Finset.sum_const (1 : ℝ)
  rw [this]
  norm_num
  -- Fin 8 has 8 elements
  rfl

/-- Ones vector is not neutral -/
lemma ones_not_neutral : ¬ IsNeutral ones := by
  unfold IsNeutral
  rw [ones_sum]
  norm_num

/-- Zero vector is neutral -/
lemma zero_neutral : IsNeutral (fun _ => 0) := by
  unfold IsNeutral windowSum
  simp [Finset.sum_const_zero]

/-- Neutrality is preserved under scalar multiplication (excluding 0 case trivially) -/
lemma neutral_scalar_mul (w : Window) (c : ℝ) (h : IsNeutral w) :
    IsNeutral (fun i => c * w i) := by
  unfold IsNeutral windowSum at *
  simp only [Finset.mul_sum]
  rw [h]
  ring

/-- Neutrality is preserved under addition -/
lemma neutral_add (w₁ w₂ : Window) (h₁ : IsNeutral w₁) (h₂ : IsNeutral w₂) :
    IsNeutral (fun i => w₁ i + w₂ i) := by
  unfold IsNeutral windowSum at *
  simp only [Finset.sum_add_distrib]
  rw [h₁, h₂]
  ring

/-- The neutral subspace is a linear subspace -/
lemma neutralSubspace_is_subspace :
    (0 : Window) ∈ NeutralSubspace ∧
    (∀ w₁ w₂ : Window, w₁ ∈ NeutralSubspace → w₂ ∈ NeutralSubspace →
      (fun i => w₁ i + w₂ i) ∈ NeutralSubspace) ∧
    (∀ (c : ℝ) (w : Window), w ∈ NeutralSubspace →
      (fun i => c * w i) ∈ NeutralSubspace) := by
  constructor
  · exact zero_neutral
  constructor
  · intros w₁ w₂ h₁ h₂
    exact neutral_add w₁ w₂ h₁ h₂
  · intros c w h
    exact neutral_scalar_mul w c h

end LightLanguage
