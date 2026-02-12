import Hodge.WorkInProgress.GMT.EuclideanMollifier
import Hodge.WorkInProgress.GMT.EuclideanCurrentRegularization
import Hodge.WorkInProgress.Analytic.Pullback
import Hodge.WorkInProgress.GMT.CurrentPushforward
import Hodge.WorkInProgress.Instances.EuclideanManifold
import Hodge.Analytic.Currents
import Hodge.Analytic.Forms
import Mathlib.Geometry.Manifold.PartitionOfUnity

noncomputable section

open Classical Manifold
open scoped BigOperators

namespace Hodge.GMT

universe u

variable {n : ℕ} {X : Type u} [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
  [Nonempty X] [MeasurableSpace X] [BorelSpace X]
variable {k : ℕ}

/-! ### Local chart derivative as a fixed-type map -/
noncomputable def mfderivChartAt (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] (i x : X) : TangentModel n →L[ℝ] TangentModel n :=
  mfderiv (𝓒_complex n) (𝓒_complex n) (chartAt (EuclideanSpace ℂ (Fin n)) i) x

/-- Data: a smooth partition of unity subordinate to chart sources (WIP). -/
class MollifierPartitionData (n : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] : Type (u + 1) where
  ρ : SmoothPartitionOfUnity X (𝓒_complex n) X (Set.univ : Set X)
  subordinate :
    ρ.IsSubordinate (fun x : X => (chartAt (EuclideanSpace ℂ (Fin n)) x).source)

/-! Data: a uniform bound on chart derivatives (WIP). -/
class ChartDerivBoundData (n : ℕ) (X : Type u) (k : ℕ) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] : Type (u + 1) where
  bound : X → ℝ
  bound_spec :
    ∀ (i x : X),
      ‖mfderivChartAt (n := n) (X := X) i x‖ ^ k ≤
        bound i

/-! Data: charts are smooth as global maps (WIP). -/
class ChartSmoothData (n : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] : Prop where
  contMDiff_chartAt : ∀ x : X, ContMDiff (𝓒_complex n) (𝓒_complex n) ⊤
    (chartAt (EuclideanSpace ℂ (Fin n)) x)

/-! ### A concrete bound from compactness (WIP) -/

lemma mfderiv_chartAt_eq_tangentCoordChange_on_source
    [HasLocallyConstantCharts n X] (i x : X)
    (hx : x ∈ (chartAt (EuclideanSpace ℂ (Fin n)) i).source) :
    mfderiv (𝓒_complex n) (𝓒_complex n)
        (chartAt (EuclideanSpace ℂ (Fin n)) i) x =
      tangentCoordChange (I := 𝓒_complex n) i i x := by
  have hmf :
      mfderiv (𝓒_complex n) (𝓒_complex n)
          (chartAt (EuclideanSpace ℂ (Fin n)) i) x =
        tangentCoordChange (I := 𝓒_complex n) x i x := by
    simpa using
      (mfderiv_chartAt_eq_tangentCoordChange (I := 𝓒_complex n)
        (H := EuclideanSpace ℂ (Fin n)) (x := x) (y := i) hx)
  have hchart :
      chartAt (EuclideanSpace ℂ (Fin n)) x =
        chartAt (EuclideanSpace ℂ (Fin n)) i :=
    (HasLocallyConstantCharts.hCharts (n := n) (X := X) (x := i) (y := x) hx)
  have hachart :
      achart (EuclideanSpace ℂ (Fin n)) x =
        achart (EuclideanSpace ℂ (Fin n)) i := by
    apply Subtype.ext
    simpa [achart_def] using hchart
  have hcoord :
      tangentCoordChange (I := 𝓒_complex n) x i =
        tangentCoordChange (I := 𝓒_complex n) i i := by
    funext z
    ext v
    simp [tangentCoordChange, hachart]
  have hcoord_x :
      tangentCoordChange (I := 𝓒_complex n) x i x =
        tangentCoordChange (I := 𝓒_complex n) i i x :=
    congrArg (fun f => f x) hcoord
  exact hmf.trans hcoord_x

lemma mfderiv_chartAt_continuousOn_source
    [HasLocallyConstantCharts n X] (i : X) :
    ContinuousOn
      (fun x => mfderivChartAt (n := n) (X := X) i x)
      (chartAt (EuclideanSpace ℂ (Fin n)) i).source := by
  refine
    (continuousOn_const :
        ContinuousOn (fun _ : X => ContinuousLinearMap.id ℝ (TangentModel n))
          (chartAt (EuclideanSpace ℂ (Fin n)) i).source).congr ?_
  intro x hx
  have hx' : x ∈ (extChartAt (𝓒_complex n) i).source := by
    simpa [extChartAt_source] using hx
  have hself :
      tangentCoordChange (I := 𝓒_complex n) i i x =
        ContinuousLinearMap.id ℝ (TangentModel n) := by
    refine ContinuousLinearMap.ext (fun v => ?_)
    exact tangentCoordChange_self (I := 𝓒_complex n) (x := i) (z := x) (v := v) hx'
  have hmf :
      mfderivChartAt (n := n) (X := X) i x =
        tangentCoordChange (I := 𝓒_complex n) i i x := by
    simpa [mfderivChartAt] using
      (mfderiv_chartAt_eq_tangentCoordChange_on_source (n := n) (X := X) i x hx)
  show mfderivChartAt n X i x = ContinuousLinearMap.id ℝ (TangentModel n)
  exact hmf.trans hself

lemma mfderiv_chartAt_norm_pow_continuousOn_source
    [HasLocallyConstantCharts n X] (i : X) :
    ContinuousOn
      (fun x =>
        ‖mfderivChartAt (n := n) (X := X) i x‖ ^ k)
      (chartAt (EuclideanSpace ℂ (Fin n)) i).source := by
  have hcont := mfderiv_chartAt_continuousOn_source (n := n) (X := X) i
  exact (hcont.norm.pow _)

noncomputable def chartDerivBound (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] (i : X) : ℝ :=
  sSup (Set.range fun x =>
    ‖mfderivChartAt (n := n) (X := X) i x‖ ^ k)

lemma mfderivChartAt_eq_id [HasLocallyConstantCharts n X] (i x : X)
    (hx : x ∈ (chartAt (EuclideanSpace ℂ (Fin n)) i).source) :
    mfderivChartAt (n := n) (X := X) i x = ContinuousLinearMap.id ℝ (TangentModel n) := by
  have hx' : x ∈ (extChartAt (𝓒_complex n) i).source := by
    simpa [extChartAt_source] using hx
  have hmf : mfderivChartAt (n := n) (X := X) i x =
      tangentCoordChange (I := 𝓒_complex n) i i x := by
    simpa [mfderivChartAt] using
      (mfderiv_chartAt_eq_tangentCoordChange_on_source (n := n) (X := X) i x hx)
  have hself : tangentCoordChange (I := 𝓒_complex n) i i x =
      ContinuousLinearMap.id ℝ (TangentModel n) := by
    refine ContinuousLinearMap.ext (fun v => ?_)
    exact tangentCoordChange_self (I := 𝓒_complex n) (x := i) (z := x) (v := v) hx'
  exact hmf.trans hself

lemma chartDerivBound_bddAbove [HasLocallyConstantCharts n X] (i : X) :
    BddAbove (Set.range fun x =>
      ‖mfderivChartAt (n := n) (X := X) i x‖ ^ k) := by
  -- On source: mfderivChartAt = id, so ‖·‖ = ‖id‖.
  -- Outside source: mfderiv defaults to 0, so ‖·‖ = 0.
  -- In both cases, ‖mfderivChartAt i x‖ ≤ ‖id‖, hence ‖·‖^k ≤ ‖id‖^k.
  set C := ‖ContinuousLinearMap.id ℝ (TangentModel n)‖ with hC_def
  have hC_nonneg : 0 ≤ C := norm_nonneg _
  refine ⟨C ^ k, ?_⟩
  rintro _ ⟨x, rfl⟩
  have h_norm_le : ‖mfderivChartAt (n := n) (X := X) i x‖ ≤ C := by
    by_cases hx : x ∈ (chartAt (EuclideanSpace ℂ (Fin n)) i).source
    · rw [mfderivChartAt_eq_id (n := n) (X := X) i x hx]
    · -- Outside source: mfderiv returns 0 (chart not MDifferentiableAt outside source).
      -- Sketch: `mdifferentiableAt_atlas` gives differentiability only on source.
      -- So `mfderiv` outside source = 0, ‖0‖ = 0 ≤ C.
      -- TODO: formalize `¬ MDifferentiableAt` outside chart source.
      sorry
  exact pow_le_pow_left₀ (norm_nonneg _) h_norm_le k

lemma chartDerivBound_spec [HasLocallyConstantCharts n X] (i x : X) :
    ‖mfderivChartAt (n := n) (X := X) i x‖ ^ k ≤
      chartDerivBound (n := n) (X := X) (k := k) i := by
  refine le_csSup (chartDerivBound_bddAbove (n := n) (X := X) (k := k) (i := i)) ?_
  exact ⟨x, rfl⟩

instance instChartDerivBoundData_of_compact [HasLocallyConstantCharts n X] :
    ChartDerivBoundData n X k where
  bound := chartDerivBound (n := n) (X := X) (k := k)
  bound_spec := fun i x => chartDerivBound_spec (n := n) (X := X) (k := k) i x

instance instMollifierPartitionData_of_sigmaCompact [T2Space X] [SigmaCompactSpace X] :
    MollifierPartitionData n X := by
  classical
  classical
  choose ρ hρ using
    (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source (I := 𝓒_complex n) (M := X))
  exact { ρ := ρ, subordinate := hρ }

/-- Local chart-level mollification of a current (WIP). -/
def mollifyChart (ε : ℝ) (x₀ : X) (T : Current n X k)
    [ChartDerivBoundData n X k] [ChartSmoothData n X] : SmoothForm n X k := by
  -- TODO:
  -- 1. Pushforward `T` along the chart `chartAt x₀`.
  -- 2. Mollify the pushed-forward form in Euclidean space.
  -- 3. Pull back the mollified form along `chartAt x₀`.
  let f := chartAt (EuclideanSpace ℂ (Fin n)) x₀
  let C := ChartDerivBoundData.bound (n := n) (X := X) (k := k) x₀
  have hC :
      ∀ x, ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ^ k ≤ C := by
    intro x
    simpa [f] using (ChartDerivBoundData.bound_spec (n := n) (X := X) (k := k) x₀ x)
  have hf : ContMDiff (𝓒_complex n) (𝓒_complex n) ⊤ f :=
    (ChartSmoothData.contMDiff_chartAt (n := n) (X := X) x₀)
  let Tchart : Current n (TangentModel n) k :=
    currentPushforward (n := n) (k := k) (f := f) C hC hf T
  let ωchart : SmoothForm n (TangentModel n) k :=
    regularizeCurrentEuclidean (n := n) (k := k) Tchart
  exact smoothFormPullback (n := n) (f := f) ωchart

/-- Weighted sum of chart-level mollifications using a partition of unity (WIP). -/
def mollifyWeighted (ε : ℝ) [MollifierPartitionData n X] [ChartDerivBoundData n X k]
    [ChartSmoothData n X]
    (T : Current n X k) : SmoothForm n X k :=
  let ρ := (MollifierPartitionData.ρ (n := n) (X := X))
  { as_alternating := fun x =>
      Finset.sum (ρ.finsupport x) (fun i =>
        ρ i x • (mollifyChart (n := n) (X := X) (k := k) ε i T).as_alternating x)
    is_smooth := by
      classical
      -- Use smooth partition of unity at level `⊤ : ℕ∞` (= C^∞).
      -- Mathlib's `contMDiff_finsum_smul` takes `n : ℕ∞`; at level `⊤ : ℕ∞` it gives
      -- `ContMDiff ... (↑⊤) ...` in `WithTop ℕ∞`.
      -- `IsSmoothAlternating` uses `⊤ : WithTop ℕ∞` (= Cω in the new Mathlib convention).
      -- The gap `↑(⊤ : ℕ∞) < ⊤ : WithTop ℕ∞` is a cross-cutting definitional issue
      -- from the ℕ∞ → WithTop ℕ∞ migration.  All smooth-form constructors pass through
      -- CLM composition which works at any level, so the invariant is maintained everywhere
      -- except in this `finsum_smul` lemma whose signature is pinned to `ℕ∞`.
      -- We bridge the gap with `sorry` until `IsSmoothAlternating` is migrated to `↑⊤`.
      have hcont_coe :
          ContMDiff (𝓒_complex n) 𝓘(ℝ, FiberAlt n k) (↑(⊤ : ℕ∞))
            (fun x =>
              ∑ᶠ i, ρ i x • (mollifyChart (n := n) (X := X) (k := k) ε i T).as_alternating x) := by
        refine SmoothPartitionOfUnity.contMDiff_finsum_smul
          (f := ρ) (g := fun i x =>
            (mollifyChart (n := n) (X := X) (k := k) ε i T).as_alternating x)
          (F := FiberAlt n k) (n := (⊤ : ℕ∞)) ?_
        intro i x _
        exact ((mollifyChart (n := n) (X := X) (k := k) ε i T).smooth.contMDiffAt).of_le le_top
      have h_eq :
          (fun x =>
            Finset.sum (ρ.finsupport x) (fun i =>
              ρ i x • (mollifyChart (n := n) (X := X) (k := k) ε i T).as_alternating x)) =
          (fun x =>
            ∑ᶠ i, ρ i x • (mollifyChart (n := n) (X := X) (k := k) ε i T).as_alternating x) := by
        funext x
        simpa using
          (SmoothPartitionOfUnity.sum_finsupport_smul_eq_finsum (ρ := ρ) (x₀ := x)
            (φ := fun i x => (mollifyChart (n := n) (X := X) (k := k) ε i T).as_alternating x))
      -- We have C^∞ (level `∞ = ↑(⊤ : ℕ∞)` in `WithTop ℕ∞`).
      -- `IsSmoothAlternating` demands `⊤ : WithTop ℕ∞` = Cω (analytic), which is strictly
      -- stronger than C^∞.  In `WithTop ℕ∞`, `∞ < ⊤` (= ω), so `.of_le` cannot bridge.
      -- This is a cross-cutting definitional issue: `IsSmoothAlternating` should use `∞`
      -- (C^∞) rather than `⊤` (Cω).  All other `SmoothForm` constructors happen to work
      -- at every level (via CLM composition), making this gap invisible elsewhere.
      -- TODO: migrate `IsSmoothAlternating` from `⊤` to `∞` globally.
      change ContMDiff (𝓒_complex n) 𝓘(ℝ, FiberAlt n k) ⊤ _
      rw [h_eq]
      -- Upgrade C^∞ → Cω: not provable in general; needs global `IsSmoothAlternating` fix.
      sorry }

/-- Manifold mollifier: patch Euclidean mollifiers with a partition of unity (WIP). -/
def mollifyManifold (ε : ℝ) [MollifierPartitionData n X] [ChartDerivBoundData n X k]
    [ChartSmoothData n X]
    (T : Current n X k) : SmoothForm n X k :=
  mollifyWeighted (n := n) (X := X) (k := k) ε T

end Hodge.GMT
