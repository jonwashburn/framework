import Hodge.Basic

import Mathlib.Geometry.Manifold.Complex
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Logic.Equiv.Fin.Basic

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

private lemma commonZeroLocus_inter {S U V : Set X} {m : ℕ} {f : Fin m → X → ℂ}
    (hSU : S ∩ U = commonZeroLocus (X := X) U m f) :
    S ∩ (U ∩ V) = commonZeroLocus (X := X) (U ∩ V) m f := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨hyS, ⟨hyU, hyV⟩⟩
    have hySU : y ∈ S ∩ U := ⟨hyS, hyU⟩
    have hyZ : y ∈ commonZeroLocus (X := X) U m f := by
      simpa [hSU] using hySU
    rcases hyZ with ⟨_hyU, hyZero⟩
    exact ⟨⟨hyU, hyV⟩, hyZero⟩
  · intro hy
    rcases hy with ⟨⟨hyU, hyV⟩, hyZero⟩
    have hyZ : y ∈ commonZeroLocus (X := X) U m f := ⟨hyU, hyZero⟩
    have hySU : y ∈ S ∩ U := by
      simpa [hSU] using hyZ
    exact ⟨hySU.1, ⟨hyU, hyV⟩⟩

instance instUnion (S T : Set X)
    [hS : IsAnalyticSetZeroLocus (n := n) (X := X) S]
    [hT : IsAnalyticSetZeroLocus (n := n) (X := X) T] :
    IsAnalyticSetZeroLocus (n := n) (X := X) (S ∪ T) where
  isClosed := hS.isClosed.union hT.isClosed
  locally_eq_zeroLocus := by
    classical
    intro x hx
    have both_case (hxS : x ∈ S) (hxT : x ∈ T) :
        ∃ (U : Set X), IsOpen U ∧ x ∈ U ∧
          ∃ (m : ℕ) (f : Fin m → X → ℂ),
            (∀ i, MDifferentiableOn (𝓒_complex n) 𝓘(ℝ, ℂ) (f i) U) ∧
              (S ∪ T) ∩ U = commonZeroLocus (X := X) U m f := by
      rcases hS.locally_eq_zeroLocus x hxS with ⟨U, hUo, hxU, mS, fS, hfS, hSU⟩
      rcases hT.locally_eq_zeroLocus x hxT with ⟨V, hVo, hxV, mT, fT, hfT, hTV⟩
      let U' : Set X := U ∩ V
      have hU'open : IsOpen U' := hUo.inter hVo
      have hxU' : x ∈ U' := ⟨hxU, hxV⟩
      have hS' : S ∩ U' = commonZeroLocus (X := X) U' mS fS := by
        simpa [U'] using
          (commonZeroLocus_inter (X := X) (S := S) (U := U) (V := V) (m := mS) (f := fS) hSU)
      have hT' : T ∩ U' = commonZeroLocus (X := X) U' mT fT := by
        have hTV' :=
          commonZeroLocus_inter (X := X) (S := T) (U := V) (V := U) (m := mT) (f := fT) hTV
        simpa [U', Set.inter_comm, Set.inter_left_comm, Set.inter_right_comm, Set.inter_assoc] using hTV'
      let fProd : Fin (mS * mT) → X → ℂ := fun i x =>
        fS ((finProdFinEquiv (m := mS) (n := mT)).symm i).1 x *
          fT ((finProdFinEquiv (m := mS) (n := mT)).symm i).2 x
      have hfProd :
          ∀ i, MDifferentiableOn (𝓒_complex n) 𝓘(ℝ, ℂ) (fProd i) U' := by
        intro i
        have hfS' :
            MDifferentiableOn (𝓒_complex n) 𝓘(ℝ, ℂ)
              (fS ((finProdFinEquiv (m := mS) (n := mT)).symm i).1) U' :=
          (hfS ((finProdFinEquiv (m := mS) (n := mT)).symm i).1).mono
            (by intro y hy; exact hy.1)
        have hfT' :
            MDifferentiableOn (𝓒_complex n) 𝓘(ℝ, ℂ)
              (fT ((finProdFinEquiv (m := mS) (n := mT)).symm i).2) U' :=
          (hfT ((finProdFinEquiv (m := mS) (n := mT)).symm i).2).mono
            (by intro y hy; exact hy.2)
        simpa [fProd] using (MDifferentiableOn.mul hfS' hfT')
      have hZeroUnion :
          commonZeroLocus (X := X) U' mS fS ∪ commonZeroLocus (X := X) U' mT fT =
            commonZeroLocus (X := X) U' (mS * mT) fProd := by
        ext y
        constructor
        · intro hy
          rcases hy with hyS | hyT
          · rcases hyS with ⟨hyU, hyS0⟩
            refine ⟨hyU, ?_⟩
            intro i
            have hzero :
                fS ((finProdFinEquiv (m := mS) (n := mT)).symm i).1 y = 0 :=
              hyS0 ((finProdFinEquiv (m := mS) (n := mT)).symm i).1
            dsimp [fProd]
            exact mul_eq_zero.mpr (Or.inl hzero)
          · rcases hyT with ⟨hyU, hyT0⟩
            refine ⟨hyU, ?_⟩
            intro i
            have hzero :
                fT ((finProdFinEquiv (m := mS) (n := mT)).symm i).2 y = 0 :=
              hyT0 ((finProdFinEquiv (m := mS) (n := mT)).symm i).2
            dsimp [fProd]
            exact mul_eq_zero.mpr (Or.inr hzero)
        · intro hy
          rcases hy with ⟨hyU, hyProd⟩
          by_cases hS0 : ∀ i, fS i y = 0
          · exact Or.inl ⟨hyU, hS0⟩
          · -- choose a nonzero fS index, force all fT to vanish
            obtain ⟨iS, hiS⟩ := not_forall.mp hS0
            have hT0 : ∀ j, fT j y = 0 := by
              intro j
              have hprod :=
                hyProd ((finProdFinEquiv (m := mS) (n := mT)) ⟨iS, j⟩)
              have hdiv :
                  (finProdFinEquiv (m := mS) (n := mT) ⟨iS, j⟩).divNat = iS := by
                exact congrArg Prod.fst
                  ((finProdFinEquiv (m := mS) (n := mT)).left_inv ⟨iS, j⟩)
              have hmod :
                  (finProdFinEquiv (m := mS) (n := mT) ⟨iS, j⟩).modNat = j := by
                exact congrArg Prod.snd
                  ((finProdFinEquiv (m := mS) (n := mT)).left_inv ⟨iS, j⟩)
              have hprod' : fS iS y * fT j y = 0 := by
                simpa [fProd, hdiv, hmod, -mul_eq_zero] using hprod
              rcases (mul_eq_zero.mp hprod') with hzero | hzero
              · exact (hiS hzero).elim
              · exact hzero
            exact Or.inr ⟨hyU, hT0⟩
      have hUnion :
          (S ∪ T) ∩ U' = commonZeroLocus (X := X) U' (mS * mT) fProd := by
        have hST :
            (S ∪ T) ∩ U' = (S ∩ U') ∪ (T ∩ U') := by
          ext y
          constructor
          · intro hy
            rcases hy with ⟨hyST, hyU⟩
            rcases hyST with hyS | hyT
            · exact Or.inl ⟨hyS, hyU⟩
            · exact Or.inr ⟨hyT, hyU⟩
          · intro hy
            rcases hy with hyS | hyT
            · exact ⟨Or.inl hyS.1, hyS.2⟩
            · exact ⟨Or.inr hyT.1, hyT.2⟩
        calc
          (S ∪ T) ∩ U' = (S ∩ U') ∪ (T ∩ U') := hST
          _ = commonZeroLocus (X := X) U' mS fS ∪ commonZeroLocus (X := X) U' mT fT := by
            simp [hS', hT']
          _ = commonZeroLocus (X := X) U' (mS * mT) fProd := hZeroUnion
      exact ⟨U', hU'open, hxU', mS * mT, fProd, hfProd, hUnion⟩
    rcases hx with hxS | hxT
    · by_cases hxT' : x ∈ T
      · exact both_case hxS hxT'
      · -- x ∈ S, x ∉ T: shrink to an open set disjoint from T
        rcases hS.locally_eq_zeroLocus x hxS with ⟨U, hUo, hxU, mS, fS, hfS, hSU⟩
        let U' : Set X := U ∩ Tᶜ
        have hU'open : IsOpen U' := hUo.inter hT.isClosed.isOpen_compl
        have hxU' : x ∈ U' := ⟨hxU, hxT'⟩
        have hS' : S ∩ U' = commonZeroLocus (X := X) U' mS fS := by
          simpa [U'] using
            (commonZeroLocus_inter (X := X) (S := S) (U := U) (V := Tᶜ) (m := mS) (f := fS) hSU)
        have hfS' :
            ∀ i, MDifferentiableOn (𝓒_complex n) 𝓘(ℝ, ℂ) (fS i) U' := by
          intro i
          exact (hfS i).mono (by intro y hy; exact hy.1)
        have hUnion : (S ∪ T) ∩ U' = commonZeroLocus (X := X) U' mS fS := by
          have hST : (S ∪ T) ∩ U' = S ∩ U' := by
            ext y
            constructor
            · intro hy
              rcases hy with ⟨hyST, hyU⟩
              rcases hyST with hyS | hyT
              · exact ⟨hyS, hyU⟩
              · exact (False.elim (by exact hyU.2 hyT))
            · intro hy
              exact ⟨Or.inl hy.1, hy.2⟩
          calc
            (S ∪ T) ∩ U' = S ∩ U' := hST
            _ = commonZeroLocus (X := X) U' mS fS := hS'
        exact ⟨U', hU'open, hxU', mS, fS, hfS', hUnion⟩
    · -- x ∈ T, x ∉ S: symmetric
      by_cases hxS' : x ∈ S
      · exact both_case hxS' hxT
      · rcases hT.locally_eq_zeroLocus x hxT with ⟨V, hVo, hxV, mT, fT, hfT, hTV⟩
        let U' : Set X := V ∩ Sᶜ
        have hU'open : IsOpen U' := hVo.inter hS.isClosed.isOpen_compl
        have hxU' : x ∈ U' := ⟨hxV, hxS'⟩
        have hT' : T ∩ U' = commonZeroLocus (X := X) U' mT fT := by
          simpa [U'] using
            (commonZeroLocus_inter (X := X) (S := T) (U := V) (V := Sᶜ) (m := mT) (f := fT) hTV)
        have hfT' :
            ∀ i, MDifferentiableOn (𝓒_complex n) 𝓘(ℝ, ℂ) (fT i) U' := by
          intro i
          exact (hfT i).mono (by intro y hy; exact hy.1)
        have hUnion : (S ∪ T) ∩ U' = commonZeroLocus (X := X) U' mT fT := by
          have hST : (S ∪ T) ∩ U' = T ∩ U' := by
            ext y
            constructor
            · intro hy
              rcases hy with ⟨hyST, hyU⟩
              rcases hyST with hyS | hyT'
              · exact (False.elim (by exact hyU.2 hyS))
              · exact ⟨hyT', hyU⟩
            · intro hy
              exact ⟨Or.inr hy.1, hy.2⟩
          calc
            (S ∪ T) ∩ U' = T ∩ U' := hST
            _ = commonZeroLocus (X := X) U' mT fT := hT'
        exact ⟨U', hU'open, hxU', mT, fT, hfT', hUnion⟩

/-- The universal set is an analytic set (it's the zero locus of the empty family of functions). -/
instance instUniv : IsAnalyticSetZeroLocus (n := n) (X := X) Set.univ where
  isClosed := isClosed_univ
  locally_eq_zeroLocus := by
    intro x hx
    -- Take any neighborhood of x, and use the empty family of functions
    refine ⟨Set.univ, isOpen_univ, mem_univ x, 0, fun _ => 0, ?_, ?_⟩
    · intro i
      -- The empty family vacuously satisfies the holomorphicity condition
      exact Fin.elim0 i
    · -- The intersection univ ∩ univ = univ equals the zero locus of the empty family
      ext y
      constructor
      · intro hy
        refine ⟨mem_univ y, ?_⟩
        intro i
        exact Fin.elim0 i
      · intro hy
        exact ⟨mem_univ y, mem_univ y⟩

/-- The empty set is an analytic set (it's the zero locus of any nonzero constant function). -/
instance instEmpty : IsAnalyticSetZeroLocus (n := n) (X := X) ∅ where
  isClosed := isClosed_empty
  locally_eq_zeroLocus := by
    intro x hx
    -- This is vacuous since x ∉ ∅
    exact False.elim hx

end IsAnalyticSetZeroLocus

end AlgGeom
end Hodge

end
