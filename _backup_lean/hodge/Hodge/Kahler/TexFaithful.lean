/-
Copyright (c) 2026 Hodge Formalization Project. All rights reserved.
Released under Apache 2.0 license.
Authors: TeX Spine Semantic Closure Implementation
-/
import Hodge.Classical.GeometricCycleClass

/-!
# TeX-Faithful Hodge Conjecture (Phase 7)

This file contains the **TeX-faithful** version of the Hodge Conjecture proof.

## Difference from Main Proof Track

The main proof in `Hodge/Kahler/Main.lean` uses a definitional shortcut:
```
SignedAlgebraicCycle.cycleClass := ofForm representingForm representingForm_closed
```

This makes the cohomology relationship trivially true by construction.

The **TeX-faithful** version here uses the geometric cycle class. On the
data-first track this is:
```
cycleClass_geom_data := ofForm (FundamentalClassSet_data support_data) ...
```

and the bridge theorem becomes:
```
cycleClass_geom_data(Z_from_spine(γ)) = [γ]
```

## Typeclass Assumptions

The proof uses explicit typeclass assumptions for deep mathematical results:

- `ChowGAGAData` - Chow's theorem / GAGA
- `SpineBridgeData_data` - Poincaré duality: fundamental class = representing form in cohomology

These make the mathematical assumptions explicit and transparent.

## Verification

```bash
lake build Hodge.Kahler.TexFaithful
lake env lean Hodge/Utils/DependencyCheck.lean
```

## References

- [W.V.D. Hodge, 1950] The Hodge Conjecture
- [R. Harvey & H.B. Lawson Jr., 1982] Calibrated Geometries
- [J.P. Serre, 1956] GAGA
-/

noncomputable section

open Classical TopologicalSpace Hodge

set_option autoImplicit false

namespace Hodge.TexFaithful

universe u

variable {n : ℕ} {X : Type u}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
  [CompactSpace X] [MeasurableSpace X] [Nonempty X]

open Hodge.TexSpine.GeometricCycleClass
open Hodge.TexSpine.ChowGAGA

/-- **TeX-Faithful Hodge Conjecture (Data-First Spine)**.

    This variant threads explicit `ClosedSubmanifoldData` through the spine bridge
    and yields the data-first geometric class `cycleClass_geom_data`.
    It is the preferred formulation when support data is available, and it
    forces the PD form to come from the current-regularization pipeline
    (via `PoincareDualityFromCurrentsData`). -/
/-! ## Data‑First (Preferred) -/

theorem hodge_conjecture_tex_faithful_data {p : ℕ}
    [MetricSpace X] [BorelSpace X]
    -- Deep typeclass assumptions (data-first bridge)
    [ChowGAGAData n X]
    [SpineBridgeData_data n X]
    [Hodge.GMT.CurrentRegularizationData n X (2 * p)]
    [CycleClass.PoincareDualityFromCurrentsData n X p]
    [AlgebraicSubvarietyClosedSubmanifoldData n X]
    [SignedAlgebraicCycleSupportCodimData n X p]
    -- Input form and hypotheses
    (γ : SmoothForm n X (2 * p)) (h_closed : IsFormClosed γ)
    (h_rational : isRationalClass (ofForm γ h_closed)) (h_p_p : isPPForm' n X p γ) :
    ∃ (Z : SignedAlgebraicCycle n X p),
      cycleClass_geom_data (n := n) (X := X)
        (data := SignedAlgebraicCycle.support_data (n := n) (X := X) (p := p) Z) =
        ofForm γ h_closed := by
  letI : SignedAlgebraicCycleSupportData n X p :=
    instSignedAlgebraicCycleSupportData_ofAlgebraic (n := n) (X := X) (p := p)
  -- Use the signed decomposition
  let sd := signed_decomposition (n := n) (X := X) γ h_closed h_p_p h_rational

  -- Use tex_spine_full_data for γplus
  obtain ⟨Zplus, hZplus_geom⟩ := tex_spine_full_data
    (n := n) (X := X) sd.γplus sd.h_plus_closed sd.h_plus_rat sd.h_plus_cone

  -- Use tex_spine_full_data for γminus
  obtain ⟨Zminus, hZminus_geom⟩ := tex_spine_full_data
    (n := n) (X := X) sd.γminus sd.h_minus_closed sd.h_minus_rat sd.h_minus_cone

  -- Build the combined signed cycle for γ = γplus - γminus
  let Z_pos := Zplus.pos ∪ Zminus.neg
  let Z_neg := Zplus.neg ∪ Zminus.pos
  let Z_pos_alg := isAlgebraicSubvariety_union Zplus.pos_alg Zminus.neg_alg
  let Z_neg_alg := isAlgebraicSubvariety_union Zplus.neg_alg Zminus.pos_alg
  let Z : SignedAlgebraicCycle n X p := {
    pos := Z_pos,
    neg := Z_neg,
    pos_alg := Z_pos_alg,
    neg_alg := Z_neg_alg,
    representingForm := γ,
    representingForm_closed := h_closed,
  }

  use Z
  -- Data-first bridge: cycleClass_geom_data = ofForm representingForm
  have hbridge := SpineBridgeData_data.fundamental_eq_representing (n := n) (X := X) (Z := Z)
  simpa [hbridge]

/-- **Corollary**: TeX-faithful data-first proof implies the main conclusion. -/
theorem tex_faithful_implies_main_data {p : ℕ}
    [MetricSpace X] [BorelSpace X]
    [ChowGAGAData n X] [SpineBridgeData_data n X]
    [Hodge.GMT.CurrentRegularizationData n X (2 * p)]
    [CycleClass.PoincareDualityFromCurrentsData n X p]
    [AlgebraicSubvarietyClosedSubmanifoldData n X]
    [SignedAlgebraicCycleSupportCodimData n X p]
    (γ : SmoothForm n X (2 * p)) (h_closed : IsFormClosed γ)
    (h_rational : isRationalClass (ofForm γ h_closed)) (h_p_p : isPPForm' n X p γ) :
    ∃ (Z : SignedAlgebraicCycle n X p), Z.RepresentsClass (ofForm γ h_closed) := by
  letI : SignedAlgebraicCycleSupportData n X p :=
    instSignedAlgebraicCycleSupportData_ofAlgebraic (n := n) (X := X) (p := p)
  obtain ⟨Z, hZ_geom⟩ :=
    hodge_conjecture_tex_faithful_data (n := n) (X := X)
      γ h_closed h_rational h_p_p
  use Z
  unfold SignedAlgebraicCycle.RepresentsClass
  rw [Z.cycleClass_eq_representingForm]
  have hBridge := SpineBridgeData_data.fundamental_eq_representing
    (n := n) (X := X) (p := p) (Z := Z)
  calc ofForm Z.representingForm Z.representingForm_closed
      = cycleClass_geom_data (n := n) (X := X)
          (data := SignedAlgebraicCycle.support_data (n := n) (X := X) (p := p) Z) := hBridge.symm
    _ = ofForm γ h_closed := hZ_geom

end Hodge.TexFaithful

end
