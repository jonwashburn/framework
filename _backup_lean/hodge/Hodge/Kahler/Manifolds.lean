import Hodge.Cohomology.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.LinearAlgebra.Alternating.Basic

/-!
# Kähler Manifolds - Core Properties

This file contains the essential theorems for Kähler manifolds that are
on the proof track of `hodge_conjecture'`.

## What's Here (ON proof track)

- `omega_isClosed` - The Kähler form is closed
- `omega_is_rational` - The Kähler class is rational
- `omega_is_pp` - The Kähler form is (1,1)
- `unitForm_isClosed` - The unit form is closed
- `unitForm_is_rational` - The unit class is rational

## What Was Archived (OFF proof track)

The following Kähler/Hodge operators are **kept off proof track** because they are not used
by `hodge_conjecture'` (yet). They live in dedicated analytic modules:

- `Hodge/Analytic/Norms.lean`: `pointwiseInner`/`L2Inner` implemented; `⋆` wired via
  `HodgeStarData.fromFiber` using the real-coordinate basis (degree `k ↦ 2n-k`)
- `Hodge/Analytic/Laplacian/Codifferential.lean`: codifferential `δ = ±⋆d⋆`
  (defined via the fiber-level ⋆; full analytic properties still pending)
- `Hodge/Analytic/Laplacian/HodgeLaplacian.lean`: Laplacian `Δ = dδ + δd` (structural; analytic properties pending)
- `Hodge/Analytic/Laplacian/HarmonicForms.lean`: harmonic predicate/interface (`IsHarmonic := Δω = 0`; analytic properties pending)
- `Hodge/Analytic/HodgeStar/*`: fiber-level infrastructure for future genuine metric-induced ⋆ construction

Run `./scripts/verify_proof_track.sh` to confirm.
-/

noncomputable section

open Classical Hodge

set_option autoImplicit false

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [ProjectiveComplexManifold n X]

variable [K : KahlerManifold n X]

theorem omega_isClosed : IsFormClosed (K.omega_form) := K.omega_closed

theorem omega_is_rational : isRationalClass ⟦K.omega_form, omega_isClosed⟧ :=
  K.omega_rational

theorem omega_is_pp : isPPForm' n X 1 K.omega_form :=
  K.omega_is_pp

omit K in
theorem unitForm_isClosed : IsFormClosed (unitForm : SmoothForm n X 0) := isFormClosed_unitForm

omit K in
theorem unitForm_is_rational : isRationalClass (n := n) (X := X) unitClass := isRationalClass_unit

/-! ## Sign Definitions

Note: The primary sign definitions are now in `Hodge/Analytic/Norms.lean` to avoid
duplicate definitions. The `hodgeStarSign` there returns `ℤ` which can be coerced
to `ℂ` when needed for scalar multiplication on `SmoothForm`. -/

end
