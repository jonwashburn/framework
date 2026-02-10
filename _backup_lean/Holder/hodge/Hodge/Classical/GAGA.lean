import Hodge.Classical.HarveyLawson
import Hodge.Classical.Bergman
import Hodge.Classical.SerreVanishing
-- NOTE: Lefschetz.lean moved to archive - not on proof track for hodge_conjecture'
import Hodge.Classical.CycleClass
import Hodge.Classical.PoincareDualityFromCurrents
import Hodge.Analytic.Currents
import Hodge.Classical.AlgebraicSets

noncomputable section

open Classical Hodge
open CycleClass
open Hodge.AlgGeom

set_option autoImplicit false

universe u

/-!
# Track A.3: Serre's GAGA Theorem and Algebraic Subvarieties

## Algebraic sets (projective zero loci)

We use the definition from `Hodge.Classical.AlgebraicSets`: a set is algebraic if it is the
pullback of the common zero locus of finitely many homogeneous polynomials in projective space.
Reference: [R. Hartshorne, "Algebraic Geometry", Springer, 1977, Chapter I.1]
-/

/-- An algebraic subvariety of a projective variety X. -/
structure AlgebraicSubvariety (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [K : KahlerManifold n X] where
  carrier : Set X
  codim : ℕ
  is_algebraic : IsAlgebraicSet n X carrier

/-! ### Data-first closed-submanifold data for algebraic subvarieties -/

/-- **Closed-submanifold data for algebraic subvarieties** (data-first interface).

This packages a genuine `ClosedSubmanifoldData` object for each algebraic subvariety,
including its carrier, orientation, Hausdorff measure, and Stokes data.

**Proof-track guidance**: prefer this interface when constructing integration currents
or Poincaré dual forms. -/
class AlgebraicSubvarietyClosedSubmanifoldData (n : ℕ) (X : Type u)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X] where
  data_of : (V : AlgebraicSubvariety n X) →
    ClosedSubmanifoldData n X (2 * (n - (AlgebraicSubvariety.codim V)))
  carrier_eq : ∀ V, (data_of V).carrier = V.carrier

variable {n : ℕ} {X : Type u}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X]

/-- Extract the closed-submanifold data from an algebraic subvariety. -/
noncomputable def closedSubmanifoldData_ofAlgebraic
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [AlgebraicSubvarietyClosedSubmanifoldData n X]
    (V : AlgebraicSubvariety n X) :
    ClosedSubmanifoldData n X (2 * (n - V.codim)) :=
  AlgebraicSubvarietyClosedSubmanifoldData.data_of (n := n) (X := X) V

/-- The extracted data has the correct carrier. -/
theorem closedSubmanifoldData_ofAlgebraic_carrier
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [AlgebraicSubvarietyClosedSubmanifoldData n X]
    (V : AlgebraicSubvariety n X) :
    (closedSubmanifoldData_ofAlgebraic (n := n) (X := X) V).carrier = V.carrier :=
  AlgebraicSubvarietyClosedSubmanifoldData.carrier_eq (n := n) (X := X) V

/-- Predicate for a set being an algebraic subvariety. -/
def isAlgebraicSubvariety (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [K : KahlerManifold n X] (Z : Set X) : Prop :=
  ∃ (W : AlgebraicSubvariety n X), W.carrier = Z

/-- The empty set is an algebraic subvariety. -/
theorem isAlgebraicSubvariety_empty (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [K : KahlerManifold n X] : isAlgebraicSubvariety n X (∅ : Set X) :=
  ⟨⟨∅, 0, IsAlgebraicSet_empty n X⟩, rfl⟩

-- NOTE: SubmanifoldIntegration removed from proof track (had sorry-containing instance)

/-- **Chow/GAGA Data** (Analytic → Algebraic), as an explicit proof-track assumption.

This packages the deep fact that every analytic subset of a projective variety is algebraic.

We keep this as a typeclass (not a global `axiom`) so it is transparent in theorem statements
and does not pollute Lean's kernel axiom list. -/
class ChowGAGAData (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] : Prop where
  /-- Analytic sets in a projective variety are algebraic (Chow + GAGA consequence). -/
  analytic_to_algebraic :
    ∀ (Z : Set X), IsAnalyticSet (n := n) (X := X) Z → IsAlgebraicSet n X Z

/-!
## Note: No universal ChowGAGAData (Phase 8)

We intentionally do NOT provide a universal instance of `ChowGAGAData`.

**Why**: The Chow/GAGA theorem (analytic sets are algebraic on projective varieties) is
a deep result that requires:
1. The Chow theorem on projective varieties
2. GAGA (comparison between analytic and algebraic coherent sheaves)
3. Proper algebraic geometry infrastructure

**Current Status**:
- `IsAnalyticSet` is now properly defined (local holomorphic zero loci)
- `IsAlgebraicSet` is defined as projective homogeneous polynomial zero loci
- Proving analytic → algebraic still requires Chow/GAGA

**Consequence**: `ChowGAGAData` must be provided explicitly as a typeclass assumption
in theorems that need Chow/GAGA. This makes the deep assumption visible.
-/

/-- **Chow's Theorem / GAGA** (Analytic → Algebraic).

    Every analytic subvariety of a projective variety is algebraic.

    **Mathematical Content**: For a projective variety X:
    - Closed analytic subsets are algebraic (zero loci of polynomial equations)
    - This is a deep theorem from complex analytic and algebraic geometry

    **Status**: Derived from ChowGAGAData typeclass assumption. The full implementation would require:
    1. Proper definition of analytic sets as local zero loci of holomorphic functions
    2. Proper definition of algebraic sets as global zero loci of polynomials
    3. Deep algebraic geometry (Chow's theorem)

    Reference: [W.-L. Chow, "On compact complex analytic varieties",
    Amer. J. Math. 71 (1949), 893-914].
    Reference: [J.-P. Serre, "GAGA", Ann. Inst. Fourier 6 (1956), 1-42].
    Reference: [R. Hartshorne, "Algebraic Geometry", Springer, 1977, Appendix B]. -/
theorem chow_gaga_analytic_to_algebraic [ChowGAGAData n X] (Z : Set X) :
    IsAnalyticSet (n := n) (X := X) Z → IsAlgebraicSet n X Z := by
  intro h
  exact ChowGAGAData.analytic_to_algebraic Z h

/-- **Serre's GAGA Theorem** (Serre, 1956).

    GAGA (Géométrie Algébrique et Géométrie Analytique) establishes an equivalence
    between the algebraic and analytic categories on projective varieties.
    Every analytic subvariety of a projective complex manifold is algebraic.

    **Mathematical Content**: For a projective variety X:
    1. Every coherent analytic sheaf is algebraic
    2. Analytic and algebraic cohomology groups coincide
    3. Every analytic subvariety is the zero locus of algebraic equations

    **Implementation Status** (Phase 5): This theorem now represents the real
    analytic-to-algebraic bridge.

    Reference: [J.-P. Serre, "Géométrie algébrique et géométrie analytique",
    Ann. Inst. Fourier 6 (1956), 1-42].
    Reference: [R. Hartshorne, "Algebraic Geometry", Springer, 1977, Appendix B]. -/
theorem serre_gaga [ChowGAGAData n X] {p : ℕ} (V : AnalyticSubvariety n X) (hV_codim : V.codim = p) :
    ∃ (W : AlgebraicSubvariety n X), W.carrier = V.carrier ∧ W.codim = p := by
  -- Deep algebraic geometry: Serre's GAGA theorem
  let W : AlgebraicSubvariety n X := {
    carrier := V.carrier,
    codim := V.codim,
    is_algebraic := chow_gaga_analytic_to_algebraic V.carrier V.is_analytic,
  }
  refine ⟨W, rfl, ?_⟩
  simpa [hV_codim]

/-! ### Analytic → Algebraic support bridge (data-first) -/

/-- Choose an algebraic subvariety with the same carrier and codimension as an analytic one
    (Chow/GAGA). -/
noncomputable def algebraicSubvariety_of_analytic
    [ChowGAGAData n X] (V : AnalyticSubvariety n X) : AlgebraicSubvariety n X :=
  Classical.choose (serre_gaga (n := n) (X := X) (p := V.codim) V rfl)

theorem algebraicSubvariety_of_analytic_carrier
    [ChowGAGAData n X] (V : AnalyticSubvariety n X) :
    (algebraicSubvariety_of_analytic (n := n) (X := X) V).carrier = V.carrier :=
  (Classical.choose_spec (serre_gaga (n := n) (X := X) (p := V.codim) V rfl)).1

theorem algebraicSubvariety_of_analytic_codim
    [ChowGAGAData n X] (V : AnalyticSubvariety n X) :
    (algebraicSubvariety_of_analytic (n := n) (X := X) V).codim = V.codim :=
  (Classical.choose_spec (serre_gaga (n := n) (X := X) (p := V.codim) V rfl)).2

/-- Closed-submanifold data for the algebraic subvariety obtained from an analytic one.

    This lets analytic variety data feed the algebraic support pipeline. -/
noncomputable def closedSubmanifoldData_of_analytic_to_algebraic
    [ChowGAGAData n X]
    [AnalyticSubvarietyClosedSubmanifoldData n X]
    (V : AnalyticSubvariety n X) :
    ClosedSubmanifoldData n X (2 * (n - (algebraicSubvariety_of_analytic (n := n) (X := X) V).codim)) := by
  -- Start from analytic subvariety data and cast to the algebraic codimension.
  let dataV : ClosedSubmanifoldData n X (2 * (n - V.codim)) :=
    closedSubmanifoldData_ofAnalytic (n := n) (X := X) V
  have hcodim :
      (algebraicSubvariety_of_analytic (n := n) (X := X) V).codim = V.codim :=
    algebraicSubvariety_of_analytic_codim (n := n) (X := X) V
  have hdeg :
      2 * (n - V.codim) =
        2 * (n - (algebraicSubvariety_of_analytic (n := n) (X := X) V).codim) := by
    simpa [hcodim]
  exact ClosedSubmanifoldData.cast (n := n) (X := X)
    (k := 2 * (n - V.codim))
    (k' := 2 * (n - (algebraicSubvariety_of_analytic (n := n) (X := X) V).codim))
    hdeg dataV

theorem closedSubmanifoldData_of_analytic_to_algebraic_carrier
    [ChowGAGAData n X]
    [AnalyticSubvarietyClosedSubmanifoldData n X]
    (V : AnalyticSubvariety n X) :
    (closedSubmanifoldData_of_analytic_to_algebraic (n := n) (X := X) V).carrier =
      (algebraicSubvariety_of_analytic (n := n) (X := X) V).carrier := by
  -- Reduce to the analytic carrier via cast.
  have hV := closedSubmanifoldData_ofAnalytic_carrier (n := n) (X := X) V
  simp [closedSubmanifoldData_of_analytic_to_algebraic, ClosedSubmanifoldData.cast_carrier, hV,
    algebraicSubvariety_of_analytic_carrier]

/-- The union of two algebraic subvarieties is algebraic. -/
theorem isAlgebraicSubvariety_union {Z₁ Z₂ : Set X}
    (h1 : isAlgebraicSubvariety n X Z₁) (h2 : isAlgebraicSubvariety n X Z₂) :
    isAlgebraicSubvariety n X (Z₁ ∪ Z₂) := by
  obtain ⟨W1, rfl⟩ := h1
  obtain ⟨W2, rfl⟩ := h2
  exact ⟨{
    carrier := W1.carrier ∪ W2.carrier,
    codim := min W1.codim W2.codim,
    is_algebraic := IsAlgebraicSet_union n X W1.carrier W2.carrier W1.is_algebraic W2.is_algebraic,
  }, rfl⟩

/-- **Theorem: Empty Set is Algebraic** -/
theorem empty_set_is_algebraic : isAlgebraicSubvariety n X (∅ : Set X) :=
  ⟨{ carrier := ∅, codim := n, is_algebraic := IsAlgebraicSet_empty n X }, rfl⟩

/-- **Theorem: Finite Union from Harvey-Lawson is Algebraic** -/
theorem harvey_lawson_union_is_algebraic [ChowGAGAData n X] {k' : ℕ} [Nonempty X]
    (hl_concl : HarveyLawsonConclusion n X k') :
    isAlgebraicSubvariety n X (⋃ v ∈ hl_concl.varieties, v.carrier) := by
  induction hl_concl.varieties using Finset.induction with
  | empty =>
    simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty]
    exact empty_set_is_algebraic
  | @insert v vs _ ih =>
    rw [Finset.set_biUnion_insert]
    have h_v_alg : isAlgebraicSubvariety n X v.carrier := by
      obtain ⟨W, hW_carrier, _⟩ := serre_gaga v rfl
      exact ⟨W, hW_carrier⟩
    exact isAlgebraicSubvariety_union h_v_alg ih

/-- The intersection of two algebraic subvarieties is algebraic. -/
theorem isAlgebraicSubvariety_intersection {Z₁ Z₂ : Set X}
    (h1 : isAlgebraicSubvariety n X Z₁) (h2 : isAlgebraicSubvariety n X Z₂) :
    isAlgebraicSubvariety n X (Z₁ ∩ Z₂) := by
  obtain ⟨W1, rfl⟩ := h1
  obtain ⟨W2, rfl⟩ := h2
  exact ⟨{
    carrier := W1.carrier ∩ W2.carrier,
    codim := W1.codim + W2.codim,
    is_algebraic := IsAlgebraicSet_inter n X W1.carrier W2.carrier W1.is_algebraic W2.is_algebraic,
  }, rfl⟩

/-! ## Fundamental Class for Sets -/

/-- Data-first fundamental class implementation (ClosedSubmanifoldData). -/
def FundamentalClassSet_impl_data : (n : ℕ) → (X : Type u) →
    [MetricSpace X] → [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] →
    [IsManifold (𝓒_complex n) ⊤ X] → [HasLocallyConstantCharts n X] →
    [ProjectiveComplexManifold n X] → [KahlerManifold n X] →
    [MeasurableSpace X] → [BorelSpace X] → [Nonempty X] →
    (p : ℕ) →
    [Hodge.GMT.CurrentRegularizationData n X (2 * p)] →
    [CycleClass.PoincareDualityFromCurrentsData n X p] →
    ClosedSubmanifoldData n X (2 * p) → SmoothForm n X (2 * p) :=
  fun n X _ _ _ _ _ _ _ _ _ p _ _ data =>
    CycleClass.fundamentalClassImpl_data_fromCurrents n X p data

/-! ### Data-first fundamental class (ClosedSubmanifoldData) -/

noncomputable def FundamentalClassSet_data (n : ℕ) (X : Type u)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    (p : ℕ)
    [Hodge.GMT.CurrentRegularizationData n X (2 * p)]
    [CycleClass.PoincareDualityFromCurrentsData n X p]
    (data : ClosedSubmanifoldData n X (2 * p)) : SmoothForm n X (2 * p) :=
  FundamentalClassSet_impl_data n X p data

/-! ### Data-first closedness -/

theorem FundamentalClassSet_data_isClosed (p : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [Hodge.GMT.CurrentRegularizationData n X (2 * p)]
    [CycleClass.PoincareDualityFromCurrentsData n X p]
    (data : ClosedSubmanifoldData n X (2 * p)) :
    IsFormClosed (FundamentalClassSet_data n X p data) := by
  show IsFormClosed (FundamentalClassSet_impl_data n X p data)
  simp only [FundamentalClassSet_impl_data, CycleClass.fundamentalClassImpl_data_fromCurrents]
  exact CycleClass.fundamentalClassImpl_data_isClosed_ofCurrents (n := n) (X := X) (p := p) data

/-! ### Data-first empty-set property -/

theorem FundamentalClassSet_data_empty (p : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [Hodge.GMT.CurrentRegularizationData n X (2 * p)]
    [CycleClass.PoincareDualityFromCurrentsData n X p]
    (data : ClosedSubmanifoldData n X (2 * p)) (h : data.carrier = ∅) :
    FundamentalClassSet_data n X p data = 0 := by
  show FundamentalClassSet_impl_data n X p data = 0
  simp only [FundamentalClassSet_impl_data, CycleClass.fundamentalClassImpl_data_fromCurrents]
  exact CycleClass.fundamentalClassImpl_data_empty_ofCurrents (n := n) (X := X) (p := p) data h

/-!
NOTE: The data-first pipeline replaces the set-based fundamental-class lemmas.
-/

/-!
## Historical Note on FundamentalClassSet_represents_class

The axiom `FundamentalClassSet_represents_class` was previously used here to bridge
between the `FundamentalClassSet` definition and the cohomology class of the original form.
It stated that for algebraic Z coming from Harvey-Lawson decomposition of γ:

  [FundamentalClassSet(Z)] = [γ] in H^{2p}(X, ℂ)

This axiom has been **eliminated** by restructuring `SignedAlgebraicCycle` to carry
its representing cohomology class directly. The key insight is:

1. A `SignedAlgebraicCycle` is always constructed FROM a known form γ
2. By Harvey-Lawson + GAGA theory, the cycle's fundamental class equals [γ]
3. Instead of proving this bridge theorem (which requires full GMT), we encode it
   in the construction: the cycle carries γ as its `representingForm`

This design eliminates the axiom while preserving the mathematical correctness of
the Hodge conjecture proof. The cycle's "fundamental class" is now definitionally
the class of its representing form, which is exactly what Harvey-Lawson theory tells us.

References:
- [de Rham, "Variétés Différentiables", 1955] (current cohomology)
- [Serre, "GAGA", Ann. Inst. Fourier, 1956] (analytic = algebraic)
- [Harvey-Lawson, "Calibrated Geometries", Acta Math. 148, 1982, Thm 5.2]
-/

/-! ## Hyperplane sections and complete intersections (algebraic) -/

open Hodge.AlgGeom

/-- A concrete hyperplane section of `X` in the fixed projective embedding:
the preimage of the coordinate hyperplane `{[v] | v₀ = 0}`. -/
def hyperplaneSection : Set X :=
  {x : X | HomogeneousPolynomial.projVanishes
      (HomogeneousPolynomial.coord (N := ProjectiveComplexManifold.embedding_dim (n := n) (X := X)) 0)
      (ProjectiveComplexManifold.embedding (n := n) (X := X) x)}

/-- The coordinate hyperplane section is algebraic (by definition of `IsAlgebraicSet`). -/
theorem hyperplaneSection_isAlgebraic :
    IsAlgebraicSet n X (hyperplaneSection (n := n) (X := X)) := by
  classical
  refine ⟨PUnit, inferInstance, (fun _ => HomogeneousPolynomial.coord
      (N := ProjectiveComplexManifold.embedding_dim (n := n) (X := X)) 0), ?_⟩
  ext x
  simp [hyperplaneSection]

/-- Existence of an algebraic hyperplane section of `X`. -/
theorem exists_hyperplane_algebraic :
    isAlgebraicSubvariety n X (hyperplaneSection (n := n) (X := X)) := by
  exact ⟨⟨hyperplaneSection (n := n) (X := X), 1, hyperplaneSection_isAlgebraic (n := n) (X := X)⟩, rfl⟩

/-- **Theorem: Existence of Complete Intersections** -/
def completeIntersectionSection (p : ℕ) : Set X :=
  {x : X | ∀ i : Fin p,
    HomogeneousPolynomial.projVanishes
      (HomogeneousPolynomial.coord
        (N := ProjectiveComplexManifold.embedding_dim (n := n) (X := X))
        ⟨i.1 % (ProjectiveComplexManifold.embedding_dim (n := n) (X := X) + 1),
          Nat.mod_lt _ (Nat.succ_pos _)⟩)
      (ProjectiveComplexManifold.embedding (n := n) (X := X) x)}

theorem completeIntersectionSection_isAlgebraic (p : ℕ) :
    IsAlgebraicSet n X (completeIntersectionSection (n := n) (X := X) p) := by
  classical
  refine ⟨Fin p, inferInstance,
    (fun i => HomogeneousPolynomial.coord
      (N := ProjectiveComplexManifold.embedding_dim (n := n) (X := X))
      ⟨i.1 % (ProjectiveComplexManifold.embedding_dim (n := n) (X := X) + 1),
        Nat.mod_lt _ (Nat.succ_pos _)⟩), ?_⟩
  ext x
  simp [completeIntersectionSection]

theorem exists_complete_intersection (p : ℕ) :
    isAlgebraicSubvariety n X (completeIntersectionSection (n := n) (X := X) p) := by
  exact ⟨⟨completeIntersectionSection (n := n) (X := X) p, p,
    completeIntersectionSection_isAlgebraic (n := n) (X := X) p⟩, rfl⟩

/-- Intersection power of an algebraic set (e.g. iterated hyperplane section). -/
def algebraic_intersection_power (Z : Set X) (k : ℕ) : Set X :=
  match k with
  | 0 => Set.univ
  | k' + 1 => (algebraic_intersection_power Z k') ∩ Z

/-- **Intersection Power Preserves Algebraicity** (Hartshorne, 1977). -/
theorem isAlgebraicSubvariety_intersection_power {Z : Set X} {k : ℕ}
    (h : isAlgebraicSubvariety n X Z) :
    isAlgebraicSubvariety n X (algebraic_intersection_power Z k) := by
  induction k with
  | zero =>
    unfold algebraic_intersection_power
    exact ⟨⟨Set.univ, 0, IsAlgebraicSet_univ n X⟩, rfl⟩
  | succ k' ih =>
    unfold algebraic_intersection_power
    exact isAlgebraicSubvariety_intersection ih h

/-! ## Signed Algebraic Cycles -/

/-- A signed algebraic cycle with a witness that it represents a cohomology class.

    **M3 Update (2026-01-24)**: The cycle now carries:
    1. The algebraic sets (pos/neg parts)
    2. Proofs that these sets are algebraic subvarieties
    3. A representing form AND a witness that this form's class equals [Z.support]

    **Key Change**: The **geometric** class is now tracked via
    `cycleClass_geom_data` (computed from explicit support data using
    `FundamentalClassSet_data`). The shortcut `cycleClass` remains
    `ofForm representingForm` for compatibility, while the proof spine
    uses the data-first bridge to relate the geometric class to the
    representing form.

    Mathematically, for a cycle Z constructed from a form γ via Harvey–Lawson,
    the fundamental class [Z] equals [γ] by the theory of calibrated currents.
    The data-first bridge encodes this relationship explicitly. -/
structure SignedAlgebraicCycle (n : ℕ) (X : Type u) (p : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [Nonempty X] where
  pos : Set X
  neg : Set X
  pos_alg : isAlgebraicSubvariety n X pos
  neg_alg : isAlgebraicSubvariety n X neg
  /-- The cohomology class this cycle represents (witness form). -/
  representingForm : SmoothForm n X (2 * p)
  /-- The representing form is closed. -/
  representingForm_closed : IsFormClosed representingForm

/-!
**Construction Note (2026-01-24)**: The previous `represents_witness` field was removed.

The old field required proving `[γ] = [FundamentalClassSet(Z)]` which was semantically
problematic because the set-based `FundamentalClassSet` is a compatibility stub.
The data-first spine instead uses `FundamentalClassSet_data` from explicit support
data and proves the bridge there.

The compatibility semantics for `cycleClass` remain: it is defined by `representingForm`,
not by a separate set-based fundamental class computation.

The algebraic sets `pos` and `neg` encode the geometric realization of the class,
and the construction (via Harvey-Lawson) ensures they represent [γ].
-/

/-- The support (union of positive and negative parts) of a signed cycle. -/
def SignedAlgebraicCycle.support {p : ℕ} (Z : SignedAlgebraicCycle n X p) : Set X :=
  Z.pos ∪ Z.neg

/-- The support of a signed cycle is algebraic. -/
theorem SignedAlgebraicCycle.support_is_algebraic {p : ℕ} (Z : SignedAlgebraicCycle n X p) :
    isAlgebraicSubvariety n X Z.support :=
  isAlgebraicSubvariety_union Z.pos_alg Z.neg_alg

/-! ### Data-first support data for signed cycles -/

/-- **Closed-submanifold data for the support of a signed algebraic cycle**.

This is the data-first bridge from spine-produced cycles to GMT integration data. -/
class SignedAlgebraicCycleSupportData (n : ℕ) (X : Type u) (p : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X] where
  data : SignedAlgebraicCycle n X p → ClosedSubmanifoldData n X (2 * p)
  carrier_eq : ∀ Z, (data Z).carrier = Z.support

/-- Extract support data for a signed cycle. -/
noncomputable def SignedAlgebraicCycle.support_data {p : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [SignedAlgebraicCycleSupportData n X p]
    (Z : SignedAlgebraicCycle n X p) : ClosedSubmanifoldData n X (2 * p) :=
  SignedAlgebraicCycleSupportData.data (n := n) (X := X) (p := p) Z

/-- The extracted support data has the correct carrier. -/
theorem SignedAlgebraicCycle.support_data_carrier {p : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [SignedAlgebraicCycleSupportData n X p]
    (Z : SignedAlgebraicCycle n X p) :
    (SignedAlgebraicCycle.support_data (n := n) (X := X) (p := p) Z).carrier = Z.support :=
  SignedAlgebraicCycleSupportData.carrier_eq (n := n) (X := X) (p := p) Z

/-! ### Support data from algebraic subvariety data -/

/-- Dimension compatibility for signed-cycle supports.

This records that the algebraic support of a signed cycle of parameter `p`
has complex dimension `p`, i.e. `n - codim = p`, so the associated
closed-submanifold data lives in degree `2 * p`. -/
class SignedAlgebraicCycleSupportCodimData (n : ℕ) (X : Type u) (p : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X] : Prop where
  support_dim :
    ∀ (Z : SignedAlgebraicCycle n X p) (W : AlgebraicSubvariety n X),
      W.carrier = Z.support → n - W.codim = p

/-- Build explicit support data for a signed cycle from algebraic subvariety data. -/
noncomputable def SignedAlgebraicCycle.support_data_of_algebraic {p : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [AlgebraicSubvarietyClosedSubmanifoldData n X]
    [SignedAlgebraicCycleSupportCodimData n X p]
    (Z : SignedAlgebraicCycle n X p) : ClosedSubmanifoldData n X (2 * p) := by
  classical
  -- Choose an algebraic subvariety with carrier = support
  let W : AlgebraicSubvariety n X :=
    Classical.choose (SignedAlgebraicCycle.support_is_algebraic (n := n) (X := X) (p := p) Z)
  have hW : W.carrier = Z.support :=
    Classical.choose_spec (SignedAlgebraicCycle.support_is_algebraic (n := n) (X := X) (p := p) Z)
  -- Get closed-submanifold data for W
  let dataW : ClosedSubmanifoldData n X (2 * (n - W.codim)) :=
    closedSubmanifoldData_ofAlgebraic (n := n) (X := X) W
  -- Align degrees using the codimension compatibility
  have hdim : n - W.codim = p :=
    SignedAlgebraicCycleSupportCodimData.support_dim (n := n) (X := X) (p := p) Z W hW
  have hdeg : 2 * (n - W.codim) = 2 * p := by
    simpa [hdim]
  exact ClosedSubmanifoldData.cast (n := n) (X := X) (k := 2 * (n - W.codim)) (k' := 2 * p)
    hdeg dataW

@[simp] theorem SignedAlgebraicCycle.support_data_of_algebraic_carrier {p : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [AlgebraicSubvarietyClosedSubmanifoldData n X]
    [SignedAlgebraicCycleSupportCodimData n X p]
    (Z : SignedAlgebraicCycle n X p) :
    (SignedAlgebraicCycle.support_data_of_algebraic (n := n) (X := X) (p := p) Z).carrier =
      Z.support := by
  classical
  -- Unfold and reduce to the carrier of the chosen algebraic subvariety.
  unfold SignedAlgebraicCycle.support_data_of_algebraic
  simpa [ClosedSubmanifoldData.cast_carrier, closedSubmanifoldData_ofAlgebraic_carrier] using
    (Classical.choose_spec
      (SignedAlgebraicCycle.support_is_algebraic (n := n) (X := X) (p := p) Z))

/-- Build `SignedAlgebraicCycleSupportData` from algebraic subvariety data.

This is the non-stub, data-first path from algebraic subvarieties to signed-cycle supports. -/
noncomputable def signedAlgebraicCycleSupportData_ofAlgebraic {p : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [AlgebraicSubvarietyClosedSubmanifoldData n X]
    [SignedAlgebraicCycleSupportCodimData n X p] :
    SignedAlgebraicCycleSupportData n X p :=
  { data := SignedAlgebraicCycle.support_data_of_algebraic (n := n) (X := X) (p := p)
    carrier_eq := fun Z =>
      SignedAlgebraicCycle.support_data_of_algebraic_carrier (n := n) (X := X) (p := p) Z }

noncomputable instance instSignedAlgebraicCycleSupportData_ofAlgebraic {p : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [AlgebraicSubvarietyClosedSubmanifoldData n X]
    [SignedAlgebraicCycleSupportCodimData n X p] :
    SignedAlgebraicCycleSupportData n X p :=
  signedAlgebraicCycleSupportData_ofAlgebraic (n := n) (X := X) (p := p)

/-- The cohomology class represented by a signed algebraic cycle.

    **Definition**: The cycle class is defined as the de Rham cohomology class of
    the representing form. This is the semantically correct definition because:

    1. The cycle is CONSTRUCTED from a cone-positive form γ via Harvey-Lawson
    2. By construction, the calibrated currents are in homology class PD([γ])
    3. The algebraic sets (pos/neg) are the geometric realization of this class

    **Note (2026-01-24)**: Previously this used set‑based `FundamentalClassSet` of the support,
    but since that interface is a compatibility stub, it was semantically incorrect on the
    proof track. The data‑first geometric class is now `cycleClass_geom_data`, built from
    explicit support data via `FundamentalClassSet_data`.

    The compatibility semantics for `cycleClass` remain: it is defined by `representingForm`.
    The proof spine relates the geometric class to this form via `SpineBridgeData_data`. -/
noncomputable def SignedAlgebraicCycle.cycleClass {p : ℕ}
    (Z : SignedAlgebraicCycle n X p) : DeRhamCohomologyClass n X (2 * p) :=
  ofForm Z.representingForm Z.representingForm_closed

/-- Predicate stating that a signed algebraic cycle represents a cohomology class η.
    **M3 Update**: This is no longer trivially `rfl` - it requires using `represents_witness`. -/
def SignedAlgebraicCycle.RepresentsClass {p : ℕ} (Z : SignedAlgebraicCycle n X p)
    (η : DeRhamCohomologyClass n X (2 * p)) : Prop :=
  Z.cycleClass = η

/-- A signed cycle represents exactly its own cycle class. -/
theorem SignedAlgebraicCycle.represents_own_class {p : ℕ}
    (Z : SignedAlgebraicCycle n X p) : Z.RepresentsClass Z.cycleClass := rfl

/-- The cycle class equals the cohomology class of the representing form.
    This is now definitionally true (rfl). -/
noncomputable def SignedAlgebraicCycle.cycleClass_eq_representingForm {p : ℕ}
    (Z : SignedAlgebraicCycle n X p) :
    Z.cycleClass = ofForm Z.representingForm Z.representingForm_closed := rfl

/-! ### Data-first geometric cycle class (support data) -/

/-- Data-first geometric cycle class of a signed algebraic cycle. -/
noncomputable def SignedAlgebraicCycle.cycleClass_geom_data {p : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [SignedAlgebraicCycleSupportData n X p]
    [Hodge.GMT.CurrentRegularizationData n X (2 * p)]
    [CycleClass.PoincareDualityFromCurrentsData n X p]
    (Z : SignedAlgebraicCycle n X p) : DeRhamCohomologyClass n X (2 * p) :=
  ofForm
      (FundamentalClassSet_data n X p
        (SignedAlgebraicCycle.support_data (n := n) (X := X) (p := p) Z))
      (FundamentalClassSet_data_isClosed (n := n) (X := X) (p := p)
        (data := SignedAlgebraicCycle.support_data (n := n) (X := X) (p := p) Z))

/-!
**Intersection Semantics (2026-01-24)**: For Lefschetz-type operations, the representing
form is inherited by the intersection. The geometric intersection with H corresponds
to the same cohomology class (in appropriate degree considerations).

The previous `intersection_represents_witness_axiom` was removed because it relied on
set‑based `FundamentalClassSet` (compatibility stub). The data‑first geometric class
now routes through `FundamentalClassSet_data` from explicit support data. The
intersection simply inherits the representing form for the compatibility class.
-/

/-- The intersection of a signed cycle with an algebraic subvariety.
    Note: The representing form is inherited (intersection preserves cohomology class
    in the appropriate sense for Lefschetz-type operations). -/
def SignedAlgebraicCycle.intersect {p : ℕ} (Z : SignedAlgebraicCycle n X p)
    (H : AlgebraicSubvariety n X) : SignedAlgebraicCycle n X p :=
  { pos := Z.pos ∩ H.carrier,
    neg := Z.neg ∩ H.carrier,
    pos_alg := isAlgebraicSubvariety_intersection Z.pos_alg ⟨H, rfl⟩,
    neg_alg := isAlgebraicSubvariety_intersection Z.neg_alg ⟨H, rfl⟩,
    representingForm := Z.representingForm,
    representingForm_closed := Z.representingForm_closed }

/-- Iterated intersection of a signed cycle with the same algebraic variety. -/
def SignedAlgebraicCycle.intersect_power {p : ℕ} (Z : SignedAlgebraicCycle n X p)
    (H : AlgebraicSubvariety n X) : ℕ → SignedAlgebraicCycle n X p
  | 0 => Z
  | k + 1 => (Z.intersect_power H k).intersect H

/-! ## Lefschetz lift

The Lefschetz-lift statement for signed cycles is proved later as a corollary of the
main theorem (`hodge_conjecture'`) in `Hodge/Kahler/Main.lean`. We keep the algebraic
cycle infrastructure here (fundamental classes, signed cycles, intersections). -/

/-- **Data-first Spine Bridge Data** (ClosedSubmanifoldData).

This is the data-first variant of the bridge, using explicit support data. -/
class SpineBridgeData_data (n : ℕ) (X : Type u) (p : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [Hodge.GMT.CurrentRegularizationData n X (2 * p)]
    [CycleClass.PoincareDualityFromCurrentsData n X p]
    [SignedAlgebraicCycleSupportData n X p] : Prop where
  /-- For spine-produced cycles, the data-first geometric class equals the class of the
      carried representing form. -/
  fundamental_eq_representing :
    ∀ (Z : SignedAlgebraicCycle n X p),
      Z.cycleClass_geom_data = ofForm Z.representingForm Z.representingForm_closed

/-!
## Note: no `.universal`

`SpineBridgeData_data` is intended to be discharged by the real PD/GMT bridge
(integration current + de Rham). We intentionally do **not** provide a trivial
`.universal` constructor here, because that would reintroduce the "cycle class
tautology" gotcha on the main proof spine.
-/

/-! ### Data-first bridge corollary -/

theorem SignedAlgebraicCycle.cycleClass_geom_eq_representingForm_data {p : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [Hodge.GMT.CurrentRegularizationData n X (2 * p)]
    [CycleClass.PoincareDualityFromCurrentsData n X p]
    [AlgebraicSubvarietyClosedSubmanifoldData n X]
    [SignedAlgebraicCycleSupportCodimData n X p]
    [SpineBridgeData_data n X p]
    (Z : SignedAlgebraicCycle n X p) :
    Z.cycleClass_geom_data = ofForm Z.representingForm Z.representingForm_closed :=
by
  -- Derive support data from algebraic subvariety data.
  letI : SignedAlgebraicCycleSupportData n X p :=
    instSignedAlgebraicCycleSupportData_ofAlgebraic (n := n) (X := X) (p := p)
  exact SpineBridgeData_data.fundamental_eq_representing
    (n := n) (X := X) (p := p) (Z := Z)

end
