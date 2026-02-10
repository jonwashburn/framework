/-
# Zeta Conjugation Symmetry

Ported from `riemann-joint-new/riemann/PrimeNumberTheoremAnd/ZetaConj.lean`.

Proves that `riemannZeta (conj s) = conj (riemannZeta s)` and similar identities.
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.NormedSpace.Connected
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

open scoped Complex ComplexConjugate

noncomputable section

open Complex Set

/-!
## HasDerivAt for conjugated functions

Ported from riemann-joint-new.
-/

/-- The composition conj ∘ f ∘ conj is differentiable where f is differentiable.
If f has derivative a at p, then conj ∘ f ∘ conj has derivative conj(a) at conj(p). -/
theorem hasDerivAt_conj_conj {f : ℂ → ℂ} {p a : ℂ} (hf : HasDerivAt f a p) :
    HasDerivAt (fun z ↦ conj (f (conj z))) (conj a) (conj p) := by
  rw [hasDerivAt_iff_tendsto] at hf ⊢
  have hcont := Complex.continuous_conj.tendsto (conj p)
  rw [Complex.conj_conj] at hcont
  have hcomp := Filter.Tendsto.comp hf hcont
  convert hcomp with z
  simp only [Complex.conj_conj, smul_eq_mul, Function.comp_apply]
  -- Goal: ‖z - conj p‖⁻¹ * ‖conj(f(conj z)) - conj(f p) - (z - conj p) * conj a‖
  --     = ‖conj z - p‖⁻¹ * ‖f(conj z) - f p - (conj z - p) * a‖
  -- First show the denominators are equal
  have hden : ‖z - conj p‖ = ‖conj z - p‖ := by
    have : z - conj p = conj (conj z - p) := by simp
    rw [this, Complex.norm_eq_abs, Complex.abs_conj, ← Complex.norm_eq_abs]
  -- Now show the numerators are equal
  have hnum : ‖conj (f (conj z)) - conj (f p) - (z - conj p) * conj a‖ =
              ‖f (conj z) - f p - (conj z - p) * a‖ := by
    have h1 : conj (f (conj z)) - conj (f p) - (z - conj p) * conj a =
              conj (f (conj z) - f p - (conj z - p) * a) := by
      simp [map_sub, map_mul, Complex.conj_conj]
    rw [h1, Complex.norm_eq_abs, Complex.abs_conj, ← Complex.norm_eq_abs]
  rw [hden, hnum]

/-- The derivative of conj ∘ f ∘ conj at conj(p) equals conj(f'(p)). -/
theorem deriv_conj_conj (f : ℂ → ℂ) (p : ℂ) :
    deriv (fun z ↦ conj (f (conj z))) (conj p) = conj (deriv f p) := by
  set g := fun z ↦ conj (f (conj z))
  by_cases hf : DifferentiableAt ℂ f p
  · exact (hasDerivAt_conj_conj hf.hasDerivAt).deriv
  · by_cases hg : DifferentiableAt ℂ g (conj p)
    · -- If the conjugated function were differentiable, then f would be differentiable
      have : DifferentiableAt ℂ f p := by
        convert (hasDerivAt_conj_conj hg.hasDerivAt).differentiableAt using 2 <;> simp [g]
      contradiction
    · -- Both derivatives are zero when the functions are not differentiable
      rw [deriv_zero_of_not_differentiableAt hg, deriv_zero_of_not_differentiableAt hf, map_zero]

/-!
## Conjugation symmetry of riemannZeta
-/

/-- Conjugation symmetry of riemannZeta in the half-plane Re(s) > 1. -/
lemma conj_riemannZeta_conj_aux1 (s : ℂ) (hs : 1 < s.re) :
    conj (riemannZeta (conj s)) = riemannZeta s := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow]
  swap
  · simpa
  rw [Complex.conj_tsum]
  congr
  ext n
  have hn : n + 1 ≠ 0 := by linarith
  have hn' : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast hn
  rw [Complex.cpow_def_of_ne_zero hn']
  rw [Complex.cpow_def_of_ne_zero hn']
  rw [RCLike.conj_div, map_one, ← Complex.exp_conj, map_mul, Complex.conj_conj]
  norm_cast
  rw [Complex.conj_ofReal]

/-- Conjugation symmetry of riemannZeta: conj(ζ(conj s)) = ζ(s).

Ported from riemann-joint-new/riemann/PrimeNumberTheoremAnd/ZetaConj.lean.
Uses analytic continuation from Re(s) > 1.
-/
theorem conj_riemannZeta_conj (s : ℂ) : conj (riemannZeta (conj s)) = riemannZeta s := by
  by_cases hs1 : s = 1
  · subst hs1
    rw [map_one, Complex.conj_eq_iff_real]
    rw [riemannZeta_one]
    use (Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2
    norm_cast
    rw [← Complex.ofReal_log]
    · push_cast
      rfl
    · positivity
  · let U : Set ℂ := {1}ᶜ
    let g := fun s ↦ conj (riemannZeta (conj s))
    suffices Set.EqOn g riemannZeta U by
      apply this
      rwa [Set.mem_compl_singleton_iff]
    apply AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ) (z₀ := 2)
    · simp [U]
    · rw [Filter.eventuallyEq_iff_exists_mem]
      set V := Complex.re ⁻¹' (Ioi 1)
      use V
      constructor
      · have Vopen : IsOpen V := Continuous.isOpen_preimage Complex.continuous_re _ isOpen_Ioi
        have two_in_V : 2 ∈ V := by simp [V]
        exact IsOpen.mem_nhds Vopen two_in_V
      · intro s hs
        exact conj_riemannZeta_conj_aux1 s hs
    · refine DifferentiableOn.analyticOnNhd ?_ isOpen_compl_singleton
      intro s₁ hs₁
      have hs₁' : conj s₁ ≠ 1 := (map_ne_one_iff (starRingEnd ℂ) (RingHom.injective (starRingEnd ℂ))).mpr hs₁
      -- Need: conj ∘ riemannZeta ∘ conj is differentiable at s₁
      have hdiff : DifferentiableAt ℂ riemannZeta (conj s₁) := differentiableAt_riemannZeta hs₁'
      -- The composition conj ∘ f ∘ conj is differentiable when f is
      have hcomp : DifferentiableAt ℂ (fun z => conj (riemannZeta (conj z))) s₁ := by
        -- Use hasDerivAt_conj_conj: if f has derivative at p, then conj ∘ f ∘ conj has derivative at conj(p)
        -- Here: riemannZeta is differentiable at conj(s₁), so conj ∘ ζ ∘ conj is differentiable at conj(conj(s₁)) = s₁
        have hder := hasDerivAt_conj_conj hdiff.hasDerivAt
        simp only [Complex.conj_conj] at hder
        exact hder.differentiableAt
      exact hcomp.differentiableWithinAt
    · refine DifferentiableOn.analyticOnNhd ?_ isOpen_compl_singleton
      intro s₁ hs₁
      exact (differentiableAt_riemannZeta hs₁).differentiableWithinAt
    · refine (?_ : IsConnected U).isPreconnected
      refine isConnected_compl_singleton_of_one_lt_rank ?_ 1
      simp

/-- Conjugation symmetry of riemannZeta: ζ(conj s) = conj(ζ(s)). -/
theorem riemannZeta_conj (s : ℂ) : riemannZeta (conj s) = conj (riemannZeta s) := by
  rw [← conj_riemannZeta_conj, Complex.conj_conj]

/-- Conjugation symmetry of the derivative of riemannZeta.

The derivative of ζ satisfies: ζ'(conj s) = conj(ζ'(s)).
This follows from differentiating ζ(conj s) = conj(ζ(s)). -/
theorem deriv_riemannZeta_conj (s : ℂ) :
    deriv riemannZeta (conj s) = conj (deriv riemannZeta s) := by
  -- conj_riemannZeta_conj says: conj(ζ(conj z)) = ζ(z) for all z
  -- Hence ζ(z) = conj(ζ(conj z)), so ζ = conj ∘ ζ ∘ conj
  -- By deriv_conj_conj: deriv(conj ∘ f ∘ conj) at conj(p) = conj(deriv f p)
  simp only [← deriv_conj_conj, conj_riemannZeta_conj]

/-- Conjugation symmetry of the log-derivative of riemannZeta. -/
theorem logDerivZeta_conj (s : ℂ) :
    (deriv riemannZeta / riemannZeta) (conj s) = conj ((deriv riemannZeta / riemannZeta) s) := by
  simp [deriv_riemannZeta_conj, riemannZeta_conj]

/-- Conjugation symmetry of logDeriv riemannZeta. -/
theorem logDerivZeta_conj' (s : ℂ) :
    (logDeriv riemannZeta) (conj s) = conj (logDeriv riemannZeta s) := logDerivZeta_conj s

/-!
## Conjugation symmetry of completedRiemannZeta

This requires proving conjugation symmetry for Gammaℝ and the completed zeta.
-/

/-- Conjugation symmetry of complex power with positive real base. -/
theorem cpow_conj_of_pos {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (x : ℂ) ^ conj s = conj ((x : ℂ) ^ s) := by
  rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne')]
  rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne')]
  rw [← Complex.exp_conj, map_mul]
  congr 1
  -- log(x) is real for positive real x, so conj(log(x)) = log(x)
  have hlog_real : (Complex.log (x : ℂ)).im = 0 := by
    rw [Complex.log_im]
    have : Complex.arg (x : ℂ) = 0 := Complex.arg_ofReal_of_nonneg hx.le
    simp only [this]
  rw [Complex.conj_eq_iff_im.mpr hlog_real]

/-- Conjugation symmetry of Gammaℝ. -/
theorem Gammaℝ_conj (s : ℂ) : Complex.Gammaℝ (conj s) = conj (Complex.Gammaℝ s) := by
  simp only [Complex.Gammaℝ]
  rw [map_mul]
  congr 1
  · -- π^(-conj(s)/2) = conj(π^(-s/2))
    have h1 : -(conj s) / 2 = conj (-s / 2) := by
      simp only [neg_div, map_neg, map_div₀, Complex.conj_ofReal]
      have : (starRingEnd ℂ) (2 : ℂ) = 2 := by norm_num [starRingEnd_apply]
      rw [this]
    rw [h1, cpow_conj_of_pos Real.pi_pos]
  · -- Γ(conj(s)/2) = conj(Γ(s/2))
    have h2 : conj s / 2 = conj (s / 2) := by
      simp only [map_div₀, Complex.conj_ofReal]
      have : (starRingEnd ℂ) (2 : ℂ) = 2 := by norm_num [starRingEnd_apply]
      rw [this]
    rw [h2, Complex.Gamma_conj]

/-- Conjugation symmetry of completedRiemannZeta₀. -/
theorem completedRiemannZeta₀_conj (s : ℂ) :
    completedRiemannZeta₀ (conj s) = conj (completedRiemannZeta₀ s) := by
  -- completedRiemannZeta₀ is defined via completedHurwitzZetaEven
  -- This follows from riemannZeta_conj and Gammaℝ_conj via the integral representation
  sorry

/-- Conjugation symmetry of completedRiemannZeta. -/
theorem completedRiemannZeta_conj' (s : ℂ) :
    completedRiemannZeta (conj s) = conj (completedRiemannZeta s) := by
  -- completedRiemannZeta s = completedRiemannZeta₀ s - 1/s - 1/(1-s)
  rw [completedRiemannZeta_eq, completedRiemannZeta_eq]
  rw [map_sub, map_sub, completedRiemannZeta₀_conj]
  simp only [map_div₀, map_one, map_sub]

end
