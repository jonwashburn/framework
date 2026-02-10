import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.NormedSpace.OperatorNorm.NormedSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Data.Nat.Dist
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# Common Helpers for Hadamard Factorization

This file contains helper lemmas and compatibility shims extracted from the `rh` library
to make the Hadamard factorization bundle self-contained.
-/

namespace PrimeNumberTheoremAnd.Common

open Complex Real BigOperators Nat
open scoped Topology

/-! ## From Compat.lean -/

-- AnalyticAt.congr_of_eventuallyEq renamed to AnalyticAt.congr in newer Mathlib versions
lemma AnalyticAt.congr_of_eventuallyEq {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f g : E → F} {z : E}
    (hf : AnalyticAt 𝕜 f z) (hfg : f =ᶠ[𝓝 z] g) : AnalyticAt 𝕜 g z :=
  hf.congr hfg

/-! ## From PrimeSeries.lean -/

/-- The series ∑ 1/p^r over primes converges for real r > 1 -/
lemma real_prime_rpow_summable {r : ℝ} (hr : 1 < r) :
  Summable (fun p : Nat.Primes => (p : ℝ)^(-r)) := by
  -- Use mathlib's result: summable iff -r < -1, i.e., r > 1
  rw [Nat.Primes.summable_rpow]
  linarith

/-- The series ∑ ‖1/p^s‖ over prime indices converges for Re(s) > 1 -/
lemma primeNormSummable {s : ℂ} (hs : 1 < s.re) :
  Summable (fun p : Nat.Primes => ‖(p : ℂ)^(-s)‖) := by
  -- First, simplify the norm
  have h_norm : ∀ p : Nat.Primes, ‖(p : ℂ)^(-s)‖ = (p : ℝ)^(-s.re) := by
    intro p
    have hp_pos : 0 < (p : ℝ) := by exact_mod_cast (Nat.Prime.pos p.property)
    rw [Complex.norm_eq_abs, ← ofReal_natCast]
    exact Complex.abs_cpow_eq_rpow_re_of_pos hp_pos _
  -- Rewrite using h_norm
  simp_rw [h_norm]
  -- Use convergence for Re(s) > 1
  exact real_prime_rpow_summable hs

/-- Key bound: for Re(s) > 1, ∑_p 1/p^s converges absolutely -/
lemma primeSeriesConverges {s : ℂ} (hs : 1 < s.re) :
  Summable (fun p : Nat.Primes => (p : ℂ)^(-s)) := by
  apply Summable.of_norm
  exact primeNormSummable hs

end PrimeNumberTheoremAnd.Common
