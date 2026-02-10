import Hodge.Basic

import Mathlib.Geometry.Manifold.Complex

/-!
# Stage 5A (Track B): Analytic sets as local holomorphic zero loci

This module is **off-proof-track** scaffolding for the plan in
`tex/archive/HodgePlan-mc-28.1.26.rtf`, Stage 5A.

Goal: introduce a *mathematically faithful* notion of complex analytic subset as a set which is
locally the common zero locus of finitely many holomorphic functions.

At this stage we only record the definition and basic consequences (e.g. closedness, when assumed).
Chow/GAGA and serious analytic geometry live downstream.
-/

noncomputable section

open Classical TopologicalSpace Set
open scoped Manifold

namespace Hodge
namespace AlgGeom

set_option autoImplicit false

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]

/-!
## Local holomorphic equations

We use Mathlib's manifold notion of complex differentiability (`MDifferentiableOn`) as the
holomorphic predicate.

For a family `f : Fin m → X → ℂ` and an open set `U`, its common zero locus in `U` is:

`{x ∈ U | ∀ i, f i x = 0}`.
-/

def commonZeroLocus (U : Set X) (m : ℕ) (f : Fin m → X → ℂ) : Set X :=
  {x | x ∈ U ∧ ∀ i, f i x = 0}

@[simp] theorem mem_commonZeroLocus {U : Set X} {m : ℕ} {f : Fin m → X → ℂ} {x : X} :
    x ∈ commonZeroLocus (X := X) U m f ↔ x ∈ U ∧ ∀ i, f i x = 0 := Iff.rfl

/-!
## Analytic sets (zero-locus presentation + closedness)

We package the *local zero-locus* data together with global closedness. The closedness field is not
redundant: “being locally a zero locus near points of `S`” alone does not imply `S` is closed.
-/

class IsAnalyticSetZeroLocus (S : Set X) : Prop where
  /-- Analytic sets are closed (classical topology). -/
  isClosed : IsClosed S
  /-- Local finite holomorphic equations near points of `S`. -/
  locally_eq_zeroLocus :
    ∀ x ∈ S, ∃ (U : Set X), IsOpen U ∧ x ∈ U ∧
      ∃ (m : ℕ) (f : Fin m → X → ℂ),
        (∀ i, MDifferentiableOn (𝓒_complex n) 𝓘(ℝ, ℂ) (f i) U) ∧
          S ∩ U = commonZeroLocus (X := X) U m f

namespace IsAnalyticSetZeroLocus

theorem isClosed' (S : Set X) [h : IsAnalyticSetZeroLocus (n := n) (X := X) S] : IsClosed S :=
  h.isClosed

instance instInter (S T : Set X)
    [hS : IsAnalyticSetZeroLocus (n := n) (X := X) S]
    [hT : IsAnalyticSetZeroLocus (n := n) (X := X) T] :
    IsAnalyticSetZeroLocus (n := n) (X := X) (S ∩ T) where
  isClosed := hS.isClosed.inter hT.isClosed
  locally_eq_zeroLocus := by
    intro x hx
    have hxS : x ∈ S := hx.1
    have hxT' : x ∈ T := hx.2
    rcases hS.locally_eq_zeroLocus x hxS with ⟨U, hUo, hxU, mS, fS, hfS, hSU⟩
    rcases hT.locally_eq_zeroLocus x hxT' with ⟨V, hVo, hxV, mT, fT, hfT, hTV⟩
    refine ⟨U ∩ V, hUo.inter hVo, ⟨hxU, hxV⟩, ?_⟩
    classical
    -- Combine the two finite families of holomorphic equations by concatenation.
    refine ⟨mS + mT, (fun i : Fin (mS + mT) =>
      (if h : (i.1 < mS) then fS ⟨i.1, h⟩ else fT ⟨i.1 - mS, by
        have hi : i.1 < mS + mT := i.2
        have hmS : mS ≤ i.1 := le_of_not_gt h
        exact Nat.sub_lt_left_of_lt_add hmS hi⟩)), ?_, ?_⟩
    · intro i
      by_cases hi : (i.1 < mS)
      · -- use the S-equations, restricted to `U ∩ V`
        have hmono : U ∩ V ⊆ U := by intro y hy; exact hy.1
        have hf' : MDifferentiableOn (𝓒_complex n) 𝓘(ℝ, ℂ) (fS ⟨i.1, hi⟩) (U ∩ V) :=
          (hfS ⟨i.1, hi⟩).mono hmono
        simpa [hi] using hf'
      · -- use the T-equations, restricted to `U ∩ V`
        have hmono : U ∩ V ⊆ V := by intro y hy; exact hy.2
        have hidx : (i.1 - mS) < mT := by
          have hi' : i.1 < mS + mT := i.2
          have hmS : mS ≤ i.1 := le_of_not_gt hi
          exact Nat.sub_lt_left_of_lt_add hmS hi'
        have hf' : MDifferentiableOn (𝓒_complex n) 𝓘(ℝ, ℂ) (fT ⟨i.1 - mS, hidx⟩) (U ∩ V) :=
          (hfT ⟨i.1 - mS, hidx⟩).mono hmono
        simpa [hi] using hf'
    · -- Set-theoretic identification of the local intersection with the combined zero locus.
      -- We use the characterizations `S ∩ U = commonZeroLocus U mS fS` and
      -- `T ∩ V = commonZeroLocus V mT fT`.
      ext y
      constructor
      · intro hy
        have hyU : y ∈ U := hy.2.1
        have hyV : y ∈ V := hy.2.2
        have hyS : y ∈ S := hy.1.1
        have hyT : y ∈ T := hy.1.2
        have hS0 : ∀ i : Fin mS, fS i y = 0 := by
          have : y ∈ commonZeroLocus (X := X) U mS fS := by
            simpa [hSU] using (show y ∈ S ∩ U from ⟨hyS, hyU⟩)
          exact this.2
        have hT0 : ∀ i : Fin mT, fT i y = 0 := by
          have : y ∈ commonZeroLocus (X := X) V mT fT := by
            simpa [hTV] using (show y ∈ T ∩ V from ⟨hyT, hyV⟩)
          exact this.2
        refine ⟨⟨hyU, hyV⟩, ?_⟩
        intro i
        by_cases hi : (i.1 < mS)
        · simpa [hi] using hS0 ⟨i.1, hi⟩
        · have hmS : mS ≤ i.1 := le_of_not_gt hi
          have hidx : (i.1 - mS) < mT := by
            have hi' : i.1 < mS + mT := i.2
            exact Nat.sub_lt_left_of_lt_add hmS hi'
          simpa [hi] using hT0 ⟨i.1 - mS, hidx⟩
      · intro hy
        -- Unpack membership in the combined zero locus.
        have hyU : y ∈ U := hy.1.1
        have hyV : y ∈ V := hy.1.2
        have h0 : ∀ i : Fin (mS + mT), (if h : (i.1 < mS) then fS ⟨i.1, h⟩ else
            fT ⟨i.1 - mS, by
              have hi : i.1 < mS + mT := i.2
              have hmS : mS ≤ i.1 := le_of_not_gt h
              exact Nat.sub_lt_left_of_lt_add hmS hi⟩) y = 0 := hy.2
        have hS0 : ∀ i : Fin mS, fS i y = 0 := by
          intro i
          have : (if h : (i.1 < mS) then fS ⟨i.1, h⟩ else
              fT ⟨i.1 - mS, by
                have hi : i.1 < mS + mT := Nat.lt_of_lt_of_le i.2 (Nat.le_add_right _ _)
                have hmS : mS ≤ i.1 := le_of_not_gt h
                exact Nat.sub_lt_left_of_lt_add hmS hi⟩) y = 0 := by
            -- here `i.1 < mS` is definitional, so the `if` selects `fS`.
            simpa using h0 ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.le_add_right _ _)⟩
          simpa using this
        have hT0 : ∀ i : Fin mT, fT i y = 0 := by
          intro i
          -- pick index `mS + i` in `Fin (mS + mT)`
          have hi' : (mS + i.1) < mS + mT := Nat.add_lt_add_left i.2 mS
          have hmS' : ¬ ((⟨mS + i.1, hi'⟩ : Fin (mS + mT)).1 < mS) := by
            simpa using Nat.not_lt.mpr (Nat.le_add_right mS i.1)
          have : (if h : ((⟨mS + i.1, hi'⟩ : Fin (mS + mT)).1 < mS) then
              fS ⟨(mS + i.1), h⟩ else
              fT ⟨(mS + i.1) - mS, by
                have hmS : mS ≤ mS + i.1 := Nat.le_add_right _ _
                exact Nat.sub_lt_left_of_lt_add hmS hi'⟩) y = 0 := by
            simpa using h0 ⟨mS + i.1, hi'⟩
          -- simplify `(mS + i) - mS = i`
          have : fT ⟨(mS + i.1) - mS, by
              have hmS : mS ≤ mS + i.1 := Nat.le_add_right _ _
              exact Nat.sub_lt_left_of_lt_add hmS hi'⟩ y = 0 := by
            simpa [hmS'] using this
          simpa [Nat.add_sub_cancel_left] using this
        -- Now recover membership in `S ∩ T` using the local characterizations.
        have hyS : y ∈ S := by
          have : y ∈ commonZeroLocus (X := X) U mS fS := ⟨hyU, hS0⟩
          have : y ∈ S ∩ U := by simpa [hSU] using this
          exact this.1
        have hyT : y ∈ T := by
          have : y ∈ commonZeroLocus (X := X) V mT fT := ⟨hyV, hT0⟩
          have : y ∈ T ∩ V := by simpa [hTV] using this
          exact this.1
        exact ⟨⟨hyS, hyT⟩, ⟨hyU, hyV⟩⟩

end IsAnalyticSetZeroLocus

end AlgGeom
end Hodge

end
