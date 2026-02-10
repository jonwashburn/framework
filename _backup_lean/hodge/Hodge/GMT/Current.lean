import Hodge.Analytic.Currents

/-!
# GMT: Currents (wrapper)

The core current infrastructure in this repository lives in `Hodge.Analytic.Currents`
and is named `Current n X k`.

The operational plan (Agent 5) uses the name `DeRhamCurrent`; we provide it here as a
compatibility alias to `Current`.
-/

noncomputable section

open Classical

set_option autoImplicit false

namespace Hodge.GMT

/-- Compatibility alias for the project’s core current type. -/
abbrev DeRhamCurrent (n : ℕ) (X : Type*) (k : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X] : Type _ :=
  Current n X k

/-- Boundary operator on currents, phrased using `Nat.sub` on degrees.

Compatibility-only: this mirrors `Current.boundary` with a `Nat`-based degree shift.
Prefer using `Current.boundary` directly on the proof track.

For `k = 0`, the boundary is defined to be `0` (since `k - 1 = 0` in `Nat`).
For `k = k' + 1`, this is `Current.boundary`. -/
def DeRhamCurrent.boundary {n : ℕ} {X : Type*}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X]
    {k : ℕ} (T : DeRhamCurrent n X k) : DeRhamCurrent n X (k - 1) := by
  cases k with
  | zero =>
    -- Nat.sub: 0 - 1 = 0
    exact (0 : DeRhamCurrent n X 0)
  | succ k' =>
    -- Nat.sub: (k'+1) - 1 = k'
    simpa [DeRhamCurrent, Nat.succ_sub_one] using (Current.boundary (k := k') T)

/-- Linearity of evaluation: `T(c • ω₁ + ω₂) = c*T(ω₁) + T(ω₂)`.

Compatibility-only: prefer the linearity lemmas on `Current` directly. -/
theorem current_eval_linear {n : ℕ} {X : Type*} {k : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X]
    (T : DeRhamCurrent n X k) (c : ℝ) (ω₁ ω₂ : SmoothForm n X k) :
    T.toFun (c • ω₁ + ω₂) = c * T.toFun ω₁ + T.toFun ω₂ :=
by
  -- `toFun` is a continuous linear map, so it is ℝ-linear.
  calc
    T.toFun (c • ω₁ + ω₂) = T.toFun (c • ω₁) + T.toFun ω₂ := by
      simpa [DeRhamCurrent] using (T.toFun.map_add (c • ω₁) ω₂)
    _ = c * T.toFun ω₁ + T.toFun ω₂ := by
      -- `c • T.toFun ω₁` is definitional `c * T.toFun ω₁` in ℝ.
      simpa [DeRhamCurrent, smul_eq_mul] using congrArg (fun x => x + T.toFun ω₂) (T.toFun.map_smul c ω₁)

end Hodge.GMT
