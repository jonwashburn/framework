import Mathlib
import IndisputableMonolith.Relativity.Geometry
import IndisputableMonolith.Relativity.Cosmology.FRWMetric

namespace IndisputableMonolith
namespace Relativity
namespace GW

open Geometry
open Cosmology

structure TensorPerturbation where
  h_TT : ℝ → (Fin 3 → Fin 3 → ℝ)
  transverse : ∀ t i, Finset.sum (Finset.range 3) (fun j =>
    if hj : j < 3 then h_TT t i ⟨j, hj⟩ else 0) = 0
  traceless : ∀ t, Finset.sum (Finset.range 3) (fun i =>
    if hi : i < 3 then h_TT t ⟨i, hi⟩ ⟨i, hi⟩ else 0) = 0

/-- Decomposition of a general spatial metric perturbation into TT part and other sectors. -/
def decompose_perturbation (h : Fin 3 → Fin 3 → ℝ) : Prop :=
  ∃ (tp : TensorPerturbation) (scalar : ℝ) (vector : Fin 3 → ℝ),
    h = (fun i j => tp.h_TT 0 i j + (if i = j then scalar else 0) + (vector i + vector j))

/-- Existence of a TT projection operator. -/
def projection_operator_TT : Prop :=
  ∃ P : (Fin 3 → Fin 3 → ℝ) → (Fin 3 → Fin 3 → ℝ),
    ∀ h, ∃ tp : TensorPerturbation, P h = tp.h_TT 0

/-- Uniqueness of the TT decomposition. -/
def decomposition_unique : Prop :=
  ∀ tp1 tp2 : TensorPerturbation, tp1.h_TT = tp2.h_TT → tp1 = tp2

theorem decomposition_unique_holds : decomposition_unique := by
  intro tp1 tp2 h
  cases tp1; cases tp2; simp at h; subst h
  rfl


end GW
end Relativity
end IndisputableMonolith
