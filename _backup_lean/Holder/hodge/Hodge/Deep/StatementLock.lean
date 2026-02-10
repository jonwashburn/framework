import Hodge.Deep

/-!
# Deep Track: Statement Lock

This file exists to **lock the types** of the deep-theorem targets we want agents to complete.

If an agent “solves” something by weakening/rewriting the statement, these checks should fail,
forcing the work to happen in proofs, not in statement surgery.

The mechanism is simple: we type-ascribe key declarations. If their types change, compilation fails.
-/

noncomputable section

open Classical

set_option autoImplicit false

namespace Hodge.Deep.StatementLock

universe u

-- ─────────────────────────────────────────────────────────────────────────────
-- Real SYR / microstructure parallel track (TeX spine step 1)
-- ─────────────────────────────────────────────────────────────────────────────

-- Lock the main “defect → 0” target statement.
#check
  (Hodge.TexSpine.microstructureSequence_real_defect_vanishes :
    ∀ {n : ℕ} {X : Type u}
      [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
      [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
      [ProjectiveComplexManifold n X] [KahlerManifold n X]
      [MeasurableSpace X] [BorelSpace X] [Nonempty X]
      [CubulationExists n X]
      (p : ℕ) (γ : SmoothForm n X (2 * p))
      (hγ : isConePositive γ) (ψ : CalibratingForm n X (2 * (n - p))),
        Filter.Tendsto
          (fun k => calibrationDefect (Hodge.TexSpine.microstructureSequence_real p γ hγ ψ k).toFun ψ)
          Filter.atTop (nhds 0))

-- NOTE: We intentionally do NOT import the legacy TeX-faithful spine modules here yet.
-- The next step is to introduce a *modern, non-quarantined* deep-track statement for the
-- spine bridge, then lock that statement here.

end Hodge.Deep.StatementLock
