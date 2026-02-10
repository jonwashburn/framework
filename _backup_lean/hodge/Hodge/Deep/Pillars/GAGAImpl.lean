import Hodge.Classical.GAGA
import Hodge.Deep.Pillars.GAGA

noncomputable section

open Classical Hodge Hodge.Deep.GAGA Hodge.AlgGeom

namespace Hodge.Deep.GAGA

variable {n : ℕ} {X : Type*}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X]

/--
**Chow's Theorem / GAGA Algebraicity Axiom**

Every closed analytic subset of a projective Kähler manifold is algebraic.

**Mathematical Content**: Chow's theorem (1949) states that every closed analytic
subvariety of projective space is algebraic. Combined with Serre's GAGA principle
(1956), this extends to coherent analytic sheaves on projective varieties. The
key idea is that analytic objects on projective varieties are "rigid" enough
to be algebraic.

Reference: [Chow, "On compact complex analytic varieties", Amer. J. Math. 71 (1949)],
[Serre, "GAGA", Ann. Inst. Fourier 6 (1956)].
-/
axiom chow_theorem_algebraicity
    (Z : Set X) (h : IsAnalyticSet (n := n) (X := X) Z) :
    IsAlgebraicSet n X Z

/--
**Chow-GAGA Instance**

Provides the `ChowGAGAData` instance required for the deep track.
Uses the Chow theorem axiom to convert analytic sets to algebraic sets.
-/
instance instChowGAGAData : ChowGAGAData n X where
  analytic_to_algebraic := fun Z h_analytic =>
    chow_theorem_algebraicity Z h_analytic

end Hodge.Deep.GAGA
