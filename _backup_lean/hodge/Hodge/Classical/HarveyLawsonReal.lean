/-
Copyright (c) 2026 Hodge Formalization Project. All rights reserved.
Released under Apache 2.0 license.
Authors: TeX Spine Semantic Closure Implementation
-/
import Hodge.Classical.HarveyLawson
import Hodge.Classical.GAGA
import Hodge.Analytic.IntegralCurrents

/-!
# Real Harvey-Lawson / King Implementation (TeX Spine Step 4)

This file provides the **real** Harvey-Lawson structure theorem and King's theorem,
following the TeX spine checklist.

## Mathematical Content

The Harvey-Lawson Structure Theorem states:

> If T is an integral current calibrated by a positive (p,p)-form ψ on a Kähler
> manifold X, then T can be written as a finite sum with positive multiplicities:
>
> T = ∑ᵢ mᵢ [Vᵢ]
>
> where each Vᵢ is a complex analytic subvariety and [Vᵢ] denotes the integration
> current over Vᵢ.

King's theorem strengthens this: if the calibrating form is the Wirtinger form (Kähler power),
then the varieties are actually holomorphic cycles.

## Main Definitions

* `HarveyLawsonKingData` - Typeclass packaging the full decomposition
* `HarveyLawsonConclusion_real` - Real structure with current equality
* `current_decomposition` - The actual sum T = ∑ mᵢ [Vᵢ]

## TeX Reference

This replaces the stub in `HarveyLawson.lean` with a real interface.

## Status

⚠️ PARALLEL TRACK - Interface for real implementation. Build with:
```bash
lake build Hodge.Classical.HarveyLawsonReal
```
-/

noncomputable section

open Classical TopologicalSpace Hodge

set_option autoImplicit false

namespace Hodge.TexSpine.HarveyLawsonKing

universe u

variable {n : ℕ} {X : Type u} {k : ℕ}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X]

/-! ## Real Harvey-Lawson Structure

The full theorem produces:
1. Finitely many analytic subvarieties V₁, ..., Vₘ
2. Positive integer multiplicities m₁, ..., mₘ
3. Current equality: T = ∑ᵢ mᵢ [Vᵢ]
-/

/-! ### Integration currents of analytic varieties (explicit interface)

These are deep GMT objects; we make them explicit as data instead of stubs. -/

class VarietyIntegrationCurrentData (n : ℕ) (X : Type*) (k : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X] where
  /-- Integration current of an analytic subvariety. -/
  current_of_variety : AnalyticSubvariety n X → Current n X k

/-- **Integration current over an analytic variety**. -/
def integrationCurrentOfVariety {k : ℕ} [VarietyIntegrationCurrentData n X k]
    (V : AnalyticSubvariety n X) : Current n X k :=
  VarietyIntegrationCurrentData.current_of_variety (n := n) (X := X) (k := k) V

/-- **Weighted sum of integration currents**.

    Given varieties Vᵢ with multiplicities mᵢ, form ∑ᵢ mᵢ [Vᵢ].

    **Implementation**: Uses a fold over the varieties. -/
def weightedCurrentSum {ι : Type*} [Fintype ι] {k : ℕ}
    [VarietyIntegrationCurrentData n X k]
    (varieties : ι → AnalyticSubvariety n X)
    (multiplicities : ι → ℕ+) : Current n X k :=
  Finset.univ.sum (fun i =>
    ((multiplicities i : ℕ) : ℤ) • integrationCurrentOfVariety (n := n) (X := X) (k := k) (varieties i))

/-- **Real Harvey-Lawson Conclusion** with current decomposition.

    Unlike the stub `HarveyLawsonConclusion` which only has a `represents` predicate,
    this structure actually provides the decomposition T = ∑ mᵢ [Vᵢ]. -/
structure HarveyLawsonConclusion_real (n : ℕ) (X : Type*) (k : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    (T : Current n X k) where
  /-- The number of varieties in the decomposition -/
  num_varieties : ℕ
  /-- The analytic subvarieties -/
  varieties : Fin num_varieties → AnalyticSubvariety n X
  /-- The positive integer multiplicities -/
  multiplicities : Fin num_varieties → ℕ+
  /-- Codimension is correct: each variety has codim = 2n - k -/
  codim_correct : ∀ i, (varieties i).codim = 2 * n - k
  /-- **Key property**: The input current equals the weighted sum of integration currents -/
  current_eq : T = weightedCurrentSum k varieties multiplicities

/-- **Real Harvey-Lawson / King Data** as a typeclass.

    This is the assumption we need for the TeX spine proof. Eventually it will
    be proved for Kähler manifolds with Wirtinger calibration. -/
class HarveyLawsonKingData (n : ℕ) (X : Type*) (k : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X] where
  /-- The decomposition theorem: given a calibrated integral current,
      produce the analytic variety decomposition. -/
  decompose : (hyp : HarveyLawsonHypothesis n X k) →
              HarveyLawsonConclusion_real n X k hyp.T.toFun

/-! ## Bridge Theorem

Connect the real implementation to the proof track.
-/

/-- **Bridge from real to stub**: the real conclusion implies the stub's represents property.

    This allows using `HarveyLawsonKingData` in the existing proof track. -/
theorem real_implies_represents [HarveyLawsonKingData n X k]
    (hyp : HarveyLawsonHypothesis n X k) :
    (harvey_lawson_theorem hyp).represents hyp.T.toFun :=
  -- The stub's represents is just `isCalibrated T ψ`, which is given by hyp
  hyp.is_calibrated

/-! ## Support of Decomposition

The union of varieties gives the support of T.
-/

/-- **Support of the Harvey-Lawson decomposition**.

    The geometric support is the union of the analytic varieties. -/
def HarveyLawsonConclusion_real.support
    {T : Current n X k} (concl : HarveyLawsonConclusion_real n X k T) : Set X :=
  ⋃ i, (concl.varieties i).carrier

/-- Indexed union over `Fin m` of analytic sets is analytic. -/
private theorem isAnalyticSet_iUnion_fin (m : ℕ) (f : Fin m → Set X)
    (hf : ∀ i, IsAnalyticSet (n := n) (X := X) (f i)) :
    IsAnalyticSet (n := n) (X := X) (⋃ i, f i) := by
  induction m with
  | zero =>
    -- Fin 0 is empty, so the union is empty
    have : (⋃ i : Fin 0, f i) = ∅ := Set.iUnion_of_empty f
    rw [this]
    exact IsAnalyticSet.empty
  | succ m ih =>
    -- Split: ⋃ i : Fin (m+1), f i = f (Fin.last m) ∪ ⋃ i : Fin m, f (Fin.castSucc i)
    have hsplit : (⋃ i : Fin (m + 1), f i) =
                  f (Fin.last m) ∪ (⋃ i : Fin m, f (Fin.castSucc i)) := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_union]
      constructor
      · intro ⟨i, hi⟩
        by_cases hlt : (i : ℕ) < m
        · right
          use ⟨i, hlt⟩
          simp only [Fin.castSucc_mk, Fin.eta, hi]
        · left
          have heq : i = Fin.last m := by
            ext
            simp only [Fin.last, Fin.val_mk]
            have := i.isLt
            omega
          rw [← heq]
          exact hi
      · intro h
        cases h with
        | inl hl => exact ⟨Fin.last m, hl⟩
        | inr hr =>
          obtain ⟨j, hj⟩ := hr
          exact ⟨Fin.castSucc j, hj⟩
    rw [hsplit]
    apply IsAnalyticSet.union
    · exact hf (Fin.last m)
    · apply ih (fun i => f (Fin.castSucc i))
      intro i
      exact hf (Fin.castSucc i)

/-- The support is an analytic set (finite union of analytic sets).

    **Proof**: Each variety is analytic, and finite unions of analytic sets
    are analytic (by `IsAnalyticSet.union` and induction on the index set). -/
theorem HarveyLawsonConclusion_real.support_isAnalytic
    {T : Current n X k} (concl : HarveyLawsonConclusion_real n X k T) :
    IsAnalyticSet (n := n) (X := X) concl.support := by
  unfold support
  apply isAnalyticSet_iUnion_fin
  intro i
  exact (concl.varieties i).is_analytic

/-! ### Analytic → Algebraic support bridge (Chow/GAGA) -/

/-- The support is an algebraic set (via Chow/GAGA). -/
theorem HarveyLawsonConclusion_real.support_isAlgebraic
    [ChowGAGAData n X]
    {T : Current n X k} (concl : HarveyLawsonConclusion_real n X k T) :
    isAlgebraicSubvariety n X concl.support := by
  -- Chow/GAGA: analytic sets are algebraic.
  refine ⟨{ carrier := concl.support
            codim := 2 * n - k
            is_algebraic := ?_ }, rfl⟩
  exact chow_gaga_analytic_to_algebraic (n := n) (X := X)
    concl.support (HarveyLawsonConclusion_real.support_isAnalytic (n := n) (X := X) (k := k) concl)

/-- An algebraic subvariety witness for the support (Chow/GAGA). -/
noncomputable def HarveyLawsonConclusion_real.support_algebraic
    [ChowGAGAData n X]
    {T : Current n X k} (concl : HarveyLawsonConclusion_real n X k T) :
    AlgebraicSubvariety n X :=
  Classical.choose (HarveyLawsonConclusion_real.support_isAlgebraic (n := n) (X := X) (k := k) concl)

theorem HarveyLawsonConclusion_real.support_algebraic_carrier
    [ChowGAGAData n X]
    {T : Current n X k} (concl : HarveyLawsonConclusion_real n X k T) :
    (HarveyLawsonConclusion_real.support_algebraic (n := n) (X := X) (k := k) concl).carrier =
      concl.support :=
  Classical.choose_spec (HarveyLawsonConclusion_real.support_isAlgebraic (n := n) (X := X) (k := k) concl)

/-- Closed-submanifold data for the Harvey–Lawson support, via algebraic subvariety data. -/
noncomputable def HarveyLawsonConclusion_real.support_data
    [ChowGAGAData n X]
    [AlgebraicSubvarietyClosedSubmanifoldData n X]
    {T : Current n X k} (concl : HarveyLawsonConclusion_real n X k T) :
    ClosedSubmanifoldData n X (2 * (n - (HarveyLawsonConclusion_real.support_algebraic
      (n := n) (X := X) (k := k) concl).codim)) :=
  closedSubmanifoldData_ofAlgebraic (n := n) (X := X)
    (HarveyLawsonConclusion_real.support_algebraic (n := n) (X := X) (k := k) concl)

theorem HarveyLawsonConclusion_real.support_data_carrier
    [ChowGAGAData n X]
    [AlgebraicSubvarietyClosedSubmanifoldData n X]
    {T : Current n X k} (concl : HarveyLawsonConclusion_real n X k T) :
    (HarveyLawsonConclusion_real.support_data (n := n) (X := X) (k := k) concl).carrier =
      concl.support := by
  -- Reduce to the carrier of the chosen algebraic subvariety.
  simpa [HarveyLawsonConclusion_real.support_data,
    closedSubmanifoldData_ofAlgebraic_carrier,
    HarveyLawsonConclusion_real.support_algebraic_carrier] 

/-! ## Harvey-Lawson Structure Theorem

Using the `HarveyLawsonKingData` typeclass (defined above at line 120).
-/

/-- **The Harvey-Lawson Structure Theorem (real version)**.

    A calibrated integral current decomposes as a sum of integration currents
    over analytic varieties.

    **Status**: Uses `HarveyLawsonKingData` typeclass to encapsulate the deep content.

    The typeclass is already defined above and makes the deep mathematical assumption explicit:
    - Regularity theory for calibrated currents (Federer)
    - Stratification theory (Harvey-Lawson)
    - King's theorem for holomorphic cycles -/
theorem harvey_lawson_king_decomposition [HarveyLawsonKingData n X k]
    (hyp : HarveyLawsonHypothesis n X k) :
    ∃ (concl : HarveyLawsonConclusion_real n X k hyp.T.toFun), concl.current_eq :=
  ⟨HarveyLawsonKingData.decompose hyp, (HarveyLawsonKingData.decompose hyp).current_eq⟩

end Hodge.TexSpine.HarveyLawsonKing

end
