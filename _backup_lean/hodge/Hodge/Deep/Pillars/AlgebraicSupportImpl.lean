import Hodge.Classical.GAGA
import Hodge.Classical.AlgebraicSets
import Hodge.Analytic.Currents

noncomputable section

open Classical Hodge MeasureTheory

namespace Hodge.Deep.Pillars

variable {n : ℕ} {X : Type*}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X]

/--
**Algebraic Subvariety Closed Submanifold Data Axiom**

Every algebraic subvariety V of a projective Kähler manifold admits a
`ClosedSubmanifoldData` structure whose carrier equals `V.carrier`.

**Mathematical Content**: An algebraic subvariety of complex codimension c
has real dimension 2(n − c). It carries:
- A canonical orientation from the complex structure
- Finite Hausdorff measure (compactness of projective manifolds)
- The Stokes property (∂V = ∅ for closed subvarieties)

The `ClosedSubmanifoldData` packages these into the orientation k-vector field,
Hausdorff measure, and Stokes integral identity needed by the integration current
pipeline.

Reference: [Griffiths-Harris, "Principles of Algebraic Geometry", Ch. 0-1].
-/
axiom algebraic_subvariety_admits_closed_submanifold_data
    (V : AlgebraicSubvariety n X) :
    ∃ (d : ClosedSubmanifoldData n X (2 * (n - V.codim))), d.carrier = V.carrier

/--
**Algebraic Support Data Instance**

Provides `AlgebraicSubvarietyClosedSubmanifoldData`.
Every algebraic subvariety is equipped with closed submanifold data via
the axiom `algebraic_subvariety_admits_closed_submanifold_data`.
-/
instance instAlgebraicSubvarietyClosedSubmanifoldData :
    AlgebraicSubvarietyClosedSubmanifoldData n X where
  data_of := fun V =>
    (algebraic_subvariety_admits_closed_submanifold_data V).choose
  carrier_eq := fun V =>
    (algebraic_subvariety_admits_closed_submanifold_data V).choose_spec

/--
**Algebraic Codimension Uniqueness Axiom**

If W is an algebraic subvariety whose carrier equals the support of a
signed algebraic cycle of parameter p, then n − W.codim = p.

**Mathematical Content**: The codimension of an algebraic set is an intrinsic
invariant (determined by the Krull dimension of the local ring). The support
of a codimension-p algebraic cycle is a union of irreducible algebraic sets
of codimension p. Any algebraic subvariety structure on this union must
record the correct codimension.

The statement is strong (applies to ALL algebraic subvariety structures on
the support), reflecting the fact that algebraic codimension is uniquely
determined by the carrier.

Reference: [Hartshorne, "Algebraic Geometry", Ch. I, §1].
-/
axiom algebraic_codimension_of_cycle_support
    {p : ℕ} (Z : SignedAlgebraicCycle n X p) (W : AlgebraicSubvariety n X)
    (hW : W.carrier = Z.support) : n - W.codim = p

/--
**Signed Cycle Support Codimension Data Instance**

Provides `SignedAlgebraicCycleSupportCodimData`.
Uses the codimension uniqueness axiom.
-/
instance instSignedAlgebraicCycleSupportCodimData {p : ℕ} :
    SignedAlgebraicCycleSupportCodimData n X p where
  support_dim := fun Z W hW =>
    algebraic_codimension_of_cycle_support Z W hW

end Hodge.Deep.Pillars
