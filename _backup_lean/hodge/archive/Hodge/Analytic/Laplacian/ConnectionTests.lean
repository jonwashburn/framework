import Hodge.Analytic.Laplacian
import Hodge.Analytic.HodgeLaplacian

/-!
# Laplacian Connection Tests (Round 3 / Agent 3)

This file is a lightweight “wiring test” that the Hodge-star → codifferential → Laplacian →
harmonic-form interfaces compose without type errors.

It is **not** intended to be mathematically deep; most operators are still semantic stubs
(e.g. adjointness / Hodge decomposition are not developed), but the definitions are arranged in
the correct shapes so the real proofs can be dropped in later with minimal churn.
-/

noncomputable section

open Classical

namespace Hodge
namespace Analytic
namespace LaplacianConnectionTests

set_option autoImplicit false

universe u

variable {n : ℕ} {X : Type u}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]

/-! ## δ² = 0 -/

theorem test_codifferential_squared_zero {k : ℕ} (ω : SmoothForm n X k) :
    True := by
  -- `δ² = 0` is recorded as an infrastructure placeholder (`True`) until the involution
  -- property of `⋆` is developed for the current fiber-level construction.
  simpa using (Codifferential.codifferential_squared_zero (n := n) (X := X) (k := k) ω)

/-! ## Δ = dδ + δd -/

theorem test_hodgeLaplacian_formula {k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ n) (ω : SmoothForm n X k) :
    HodgeLaplacian.hodgeLaplacian_construct (n := n) (X := X) (k := k) hk hk' ω =
      castForm (by omega)
          (smoothExtDeriv (Codifferential.codifferential (n := n) (X := X) (k := k) ω)) +
        (if hkn : k = n then
          0
        else
          castForm (by
            have : k ≤ n := hk'
            -- The degree cast is the same one used in `laplacian_construct`.
            simpa using
              (show n - (n - (k + 1) + 1) = k from by
                have hklt : k < n := lt_of_le_of_ne this hkn
                have hk1 : 1 ≤ n - k := (Nat.succ_le_iff).2 (Nat.sub_pos_of_lt hklt)
                have hnk : n - (k + 1) + 1 = n - k := by
                  calc
                    n - (k + 1) + 1 = (n - Nat.succ k) + 1 := by
                      rw [Nat.add_one k]
                    _ = (n - k - 1) + 1 := by
                      exact congrArg (fun t => t + 1) (Nat.sub_succ n k)
                    _ = n - k := by simpa using (Nat.sub_add_cancel hk1)
                calc
                  n - (n - (k + 1) + 1) = n - (n - k) := by simpa [hnk]
                  _ = k := Nat.sub_sub_self hk'))
            (Codifferential.codifferential (n := n) (X := X) (k := k + 1) (smoothExtDeriv ω))) := by
  rfl

/-! ## Harmonic = ker(Δ) (definition) -/

theorem test_isHarmonic_def {k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ n) (ω : SmoothForm n X k) :
    HarmonicForms.IsHarmonic (n := n) (X := X) (k := k) hk hk' ω ↔
      HodgeLaplacian.laplacian_construct (n := n) (X := X) (k := k) hk hk' ω = 0 :=
  Iff.rfl

/-! ## Cross-module wiring smoke test -/

theorem test_laplacian_compiles {k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ n) (ω : SmoothForm n X k) : True := by
  let _ : SmoothForm n X k :=
    HodgeLaplacian.hodgeLaplacian_construct (n := n) (X := X) (k := k) hk hk' ω
  trivial

end LaplacianConnectionTests
end Analytic
end Hodge
