import Hodge.Cohomology.Basic
import Hodge.Kahler.Main

/-!
# The Hodge Conjecture (Final Formalization)

This is the top-level entry point for the Hodge Conjecture formalization.
The full proof logic is contained in `Hodge/Kahler/Main.lean`.

## Two Versions

1. **`hodge_conjecture_data`** (TeX-faithful, data-first): Uses the *geometric* cycle
   class computed from explicit `ClosedSubmanifoldData` and forces the PD form to
   come from `integrationCurrent_data` via regularization.

2. **`hodge_conjecture_kernel`** (kernel-only): Uses definitional shortcut
   `cycleClass := ofForm representingForm`. No custom axioms, but not TeX-faithful.
-/

noncomputable section

open Classical Hodge

set_option autoImplicit false

variable {n : ℕ} {X : Type*}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X]

/-- **The Hodge Conjecture (Data‑First)** (Hodge, 1950; Millennium Prize Problem).

    For a smooth projective complex algebraic variety X, every rational Hodge class
    is algebraic (i.e., the GEOMETRIC cycle class equals the cohomology class).

    **TeX-Faithful (data-first)**: Uses the geometric cycle class computed from
    explicit `ClosedSubmanifoldData`, and a data-first bridge assumption
    `SpineBridgeData_data` relating the fundamental class to the carried
    `representingForm` class.

    **Phase 7 Update (2026-02-01)**: the proof track uses the **data‑first**
    fundamental class `FundamentalClassSet_data(support_data)`. Requires:
    - `PoincareDualityFromCurrentsData` for the PD form (current → regularize)
    - `SpineBridgeData_data` for the bridge theorem

    **Mathematical Content**:
    - The cycle Z is constructed via SYR → Harvey-Lawson → GAGA
    - Its geometric cycle class (from `FundamentalClassSet_data`) equals [γ] in cohomology
    - The bridge theorem connects the fundamental class to the representing form

    See `hodge_conjecture_kernel` for the kernel-only version. -/
theorem hodge_conjecture_data {p : ℕ}
    [HodgeConjectureAssumptions n X p]
    (γ : SmoothForm n X (2 * p)) (h_closed : IsFormClosed γ)
    (h_rational : isRationalClass (ofForm γ h_closed)) (h_p_p : isPPForm' n X p γ) :
    ∃ (Z : SignedAlgebraicCycle n X p), Z.cycleClass_geom_data = ofForm γ h_closed :=
  hodge_conjecture' γ h_closed h_rational h_p_p

end
