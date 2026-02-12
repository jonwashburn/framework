import Hodge.Classical.FedererFleming
import Hodge.Deep.Pillars.FedererFleming

noncomputable section

open Classical Hodge Hodge.GMT Filter

namespace Hodge.Deep.FedererFleming

variable {n : ℕ} {X : Type*}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X]

/--
**Federer-Fleming Compactness Axiom**

Every sequence of integral k-currents with uniformly bounded mass and boundary mass
has a subsequence converging in flat norm to an integral current.

**Mathematical Content**: This is the foundational compactness theorem for
integral currents (Federer-Fleming 1960, Theorem 6.8). The proof combines:
1. Banach-Alaoglu: weak*-compactness of mass-bounded currents on compact manifolds
2. Deformation Theorem: flat norm topology ↔ weak* topology on normal currents
3. Closure Theorem: flat-norm limits of integral currents are integral

Reference: [Federer-Fleming, "Normal and integral currents", Ann. Math. 72 (1960)],
[Federer, "Geometric Measure Theory", §4.2.17 (1969)],
[Simon, "Lectures on Geometric Measure Theory", Ch. 7 (1983)].
-/
axiom federer_fleming_compactness {k : ℕ}
    (T_seq : ℕ → IntegralCurrent n X k) (M : ℝ)
    (hM : ∀ j, (T_seq j : Current n X k).mass + (boundaryHL (T_seq j : Current n X k)).mass ≤ M) :
    ∃ (T_limit : IntegralCurrent n X k) (φ : ℕ → ℕ),
      StrictMono φ ∧
      Tendsto (fun j => flatNorm ((T_seq (φ j) : Current n X k) - T_limit.toFun)) atTop (nhds 0)

/--
**Federer-Fleming Compactness Instance**

Provides the `FlatLimitExistenceData` instance required for the deep track.
Uses the Federer-Fleming compactness axiom.
-/
instance instFlatLimitExistenceData {k : ℕ} : FlatLimitExistenceData n X k where
  flat_limit_existence := fun T_seq M hM =>
    federer_fleming_compactness T_seq M hM

end Hodge.Deep.FedererFleming
