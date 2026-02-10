import Hodge.Classical.HarveyLawson

/-!
# GMT: Harvey–Lawson structure theorem (wrapper)

The operational plan references a GMT-layer file `Hodge/GMT/HarveyLawsonTheorem.lean`.

This repository already contains a **proof-track-safe semantic stub** of the Harvey–Lawson
structure theorem in `Hodge/Classical/HarveyLawson.lean` (see `harvey_lawson_theorem`).

To match the planned module layout without duplicating definitions, this file simply re-exports
the relevant interfaces in the `Hodge.GMT` namespace.

This module is **not** imported by the proof-track entry point, so it can evolve independently.
-/

noncomputable section

open Classical

set_option autoImplicit false

namespace Hodge.GMT

universe u

variable {n : ℕ} {X : Type u}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X] [Nonempty X]
  [MeasurableSpace X] [BorelSpace X]

/-! ## Re-exports -/

abbrev AnalyticSubvariety := _root_.AnalyticSubvariety n X

abbrev HarveyLawsonHypothesis (k : ℕ) := _root_.HarveyLawsonHypothesis n X k

abbrev HarveyLawsonConclusion (k : ℕ) := _root_.HarveyLawsonConclusion n X k

/-- Harvey–Lawson structure theorem (semantic stub), as provided in `Hodge/Classical/HarveyLawson.lean`. -/
def harveyLawsonTheorem {k : ℕ} [HarveyLawsonKingData n X k]
    (hyp : _root_.HarveyLawsonHypothesis n X k) :
    _root_.HarveyLawsonConclusion n X k :=
  harvey_lawson_theorem hyp

theorem harveyLawson_represents {k : ℕ} [HarveyLawsonKingData n X k]
    (hyp : _root_.HarveyLawsonHypothesis n X k) :
    (harveyLawsonTheorem hyp).represents hyp.T.toFun :=
  harvey_lawson_represents hyp

end Hodge.GMT
