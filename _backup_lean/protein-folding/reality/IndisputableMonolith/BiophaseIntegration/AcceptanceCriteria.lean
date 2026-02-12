import Mathlib
import Lean.Data.Json
import IndisputableMonolith.BiophaseCore.Constants
import IndisputableMonolith.BiophaseCore.Specification
import IndisputableMonolith.BiophaseIntegration.DataIO

/-!
# Acceptance Criteria: ρ, SNR, and Circular Variance

Formalize the three statistical acceptance criteria for BIOPHASE:
1. Correlation ρ ≥ 0.30 (Pearson correlation coefficient)
2. SNR ≥ 5σ (signal-to-noise ratio)
3. Circular variance ≤ 0.40 (phase coherence)

These criteria ensure robust, phase-coherent signals aligned with
the eight-beat structure.
-/

namespace IndisputableMonolith
namespace BiophaseIntegration

open scoped BigOperators

namespace Stats

open Classical

/-- Mean of a list with empty-list fallback to `0`. -/
noncomputable def mean (xs : List ℝ) : ℝ :=
  if h : xs.length = 0 then
    0
  else
    xs.sum / xs.length

/-- Centered version of a list: subtract the mean from each entry. -/
noncomputable def centered (xs : List ℝ) : List ℝ :=
  let μ := mean xs
  xs.map fun x => x - μ

/-- Variance proxy: sum of squared centered values (unnormalized). -/
noncomputable def variance (xs : List ℝ) : ℝ :=
  (centered xs |>.map fun x => x^2).sum

/-- Pointwise difference of two sequences (zips to shortest length). -/
def differenceList (xs ys : List ℝ) : List ℝ :=
  List.zipWith (fun x y => x - y) xs ys

/-- Residuals between signal/reference data, defaulting to mean-centering. -/
noncomputable def residuals (signal reference : List ℝ) : List ℝ :=
  if hlen : reference.length = signal.length ∧ 0 < signal.length then
    differenceList signal reference
  else
    let μ := mean signal
    signal.map fun s => s - μ

/-- Root-mean-square value with empty fallback. -/
noncomputable def rootMeanSquare (xs : List ℝ) : ℝ :=
  if h : xs.length = 0 then
    0
  else
    Real.sqrt ((xs.map fun x => x^2).sum / xs.length)

/-- RMS-based SNR with numerical guard rails. -/
noncomputable def signalToNoiseRatio (signal reference : List ℝ) : ℝ :=
  let sRms := rootMeanSquare signal
  let nRms := rootMeanSquare (residuals signal reference)
  let denom := max nRms (1e-9)
  sRms / denom

/-- Optional mean helper powering conversions. -/
def optionalMean (xs : List ℝ) : Option ℝ :=
  match xs with
  | [] => none
  | _ => some (mean xs)

/-- Encode real numbers as JSON strings (avoids rational coercions). -/
def jsonOfReal (r : ℝ) : Json :=
  Json.str (toString r)

/-- Covariance proxy between two sequences (unnormalized). -/
noncomputable def covariance (x y : List ℝ) : ℝ :=
  if hxy : x.length = y.length then
    let n := x.length
    let mean_x := mean x
    let mean_y := mean y
    let hy : y.length = n := by simpa [n] using hxy
    ∑ i : Fin n,
      (x.get i - mean_x) * (y.get (Fin.cast hy.symm i) - mean_y)
  else
    0

/-- Variance is always nonnegative. -/
lemma variance_nonneg (xs : List ℝ) : 0 ≤ variance xs := by
  unfold variance centered
  apply List.sum_nonneg
  intro y _
  exact sq_nonneg _

lemma sum_map_eq_sum_fin {α β} [AddCommMonoid β] (xs : List α) (f : α → β) :
    (xs.map f).sum = ∑ i : Fin xs.length, f (xs.get i) := by
  classical
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simpa [List.map, Fin.sum_univ_succ, ih]

lemma variance_eq_sum (xs : List ℝ) :
    variance xs = ∑ i : Fin xs.length, (xs.get i - mean xs)^2 := by
  classical
  unfold variance centered
  have := sum_map_eq_sum_fin xs (fun x => (x - mean xs)^2)
  simpa using this

lemma covariance_eq_sum (x y : List ℝ) (hxy : x.length = y.length) :
    covariance x y =
      ∑ i : Fin x.length,
        (x.get i - mean x) * (y.get (Fin.cast hxy.symm i) - mean y) := by
  classical
  unfold covariance
  have hy : y.length = x.length := hxy.symm
  have hx : x.length = y.length := hxy
  simp [hx, hy]

lemma covariance_self (x : List ℝ) : covariance x x = variance x := by
  classical
  unfold covariance
  simp [variance, centered, List.map_map, sq, mul_comm, mul_left_comm, mul_assoc]

end Stats

/-! ## Pearson Correlation Coefficient -/

open Classical

/-- Pearson correlation coefficient for two sequences. -/
noncomputable def pearson_correlation (x y : List ℝ) : ℝ :=
  if hxy : x.length = y.length ∧ 0 < x.length then
    let var_x := Stats.variance x
    let var_y := Stats.variance y
    let cov := Stats.covariance x y
    if hvar : var_x = 0 ∨ var_y = 0 then
      if hx : x = y then 1 else 0
    else
      cov / Real.sqrt (var_x * var_y)
  else
    0

lemma pearson_correlation_abs_le_one (x y : List ℝ) :
    |pearson_correlation x y| ≤ (1 : ℝ) := by
  classical
  by_cases hxy : x.length = y.length ∧ 0 < x.length
  · rcases hxy with ⟨hxlen, hxpos⟩
    set var_x := Stats.variance x
    set var_y := Stats.variance y
    set cov := Stats.covariance x y
    have hvar_nonneg_x : 0 ≤ var_x := Stats.variance_nonneg x
    have hvar_nonneg_y : 0 ≤ var_y := Stats.variance_nonneg y
    by_cases hvar : var_x = 0 ∨ var_y = 0
    · by_cases hx : x = y
      · simp [pearson_correlation, hxy, hvar, hx]
      · simp [pearson_correlation, hxy, hvar, hx]
    · have hvarx_ne : var_x ≠ 0 := by
        intro hx0
        exact hvar (Or.inl hx0)
      have hvary_ne : var_y ≠ 0 := by
        intro hy0
        exact hvar (Or.inr hy0)
      have hvarx_pos : 0 < var_x := by
        by_contra hxle
        have hxle' : var_x ≤ 0 := le_of_not_gt hxle
        have hxzero : var_x = 0 := le_antisymm hvar_nonneg_x hxle'
        exact hvarx_ne hxzero
      have hvary_pos : 0 < var_y := by
        by_contra hyle
        have hyle' : var_y ≤ 0 := le_of_not_gt hyle
        have hyzero : var_y = 0 := le_antisymm hvar_nonneg_y hyle'
        exact hvary_ne hyzero
      let n := x.length
      have hylen : y.length = n := by simpa [n] using hxlen
      let u : Fin n → ℝ := fun i => x.get i - Stats.mean x
      let v : Fin n → ℝ := fun i => y.get (Fin.cast hylen.symm i) - Stats.mean y
      have hcov_sum : cov = ∑ i : Fin n, u i * v i := by
        have := Stats.covariance_eq_sum x y hxlen
        simpa [cov, n, u, v, hylen]
      have hvarx_sum : var_x = ∑ i : Fin n, (u i)^2 := by
        have := Stats.variance_eq_sum x
        simpa [var_x, n, u]
      have hvary_sum : var_y = ∑ i : Fin n, (v i)^2 := by
        have := Stats.variance_eq_sum y
        simpa [var_y, n, v, hylen]
      have hinner : cov = Real.inner u v := by
        simp [hcov_sum, u, v] at *
        simpa using hcov_sum
      have hnorm_u_sq : var_x = ‖u‖ ^ 2 := by
        have hnorm := (Real.norm_sq_eq_inner u)
        have hinner_self : Real.inner u u = ∑ i : Fin n, (u i) * (u i) := by
          simp [u]
        simpa [hnorm, hinner_self, hvarx_sum, sq]
      have hnorm_v_sq : var_y = ‖v‖ ^ 2 := by
        have hnorm := (Real.norm_sq_eq_inner v)
        have hinner_self : Real.inner v v = ∑ i : Fin n, (v i) * (v i) := by
          simp [v]
        simpa [hnorm, hinner_self, hvary_sum, sq]
      have hcs := abs_real_inner_le_norm u v
      have hcov_abs : |cov| ≤ ‖u‖ * ‖v‖ := by
        simpa [hinner]
      have hsqrt_var_x : Real.sqrt var_x = ‖u‖ := by
        have hnorm := Real.sqrt_sq (norm_nonneg u)
        simpa [var_x, hnorm_u_sq] using hnorm
      have hsqrt_var_y : Real.sqrt var_y = ‖v‖ := by
        have hnorm := Real.sqrt_sq (norm_nonneg v)
        simpa [var_y, hnorm_v_sq] using hnorm
      have hnorm_mul_eq : ‖u‖ * ‖v‖ = Real.sqrt (var_x * var_y) := by
        have := Real.sqrt_mul hvar_nonneg_x hvar_nonneg_y
        simpa [hsqrt_var_x, hsqrt_var_y, mul_comm, mul_left_comm, mul_assoc]
          using this.symm
      have hcov_abs' : |cov| ≤ Real.sqrt (var_x * var_y) :=
        by simpa [hnorm_mul_eq] using hcov_abs
      have hden_pos : 0 < Real.sqrt (var_x * var_y) :=
        Real.sqrt_pos.mpr (mul_pos hvarx_pos hvary_pos)
      have hbound_div : |cov| / Real.sqrt (var_x * var_y) ≤ 1 :=
        (div_le_iff_of_pos hden_pos).mpr (by simpa using hcov_abs')
      have habs_eq : |cov / Real.sqrt (var_x * var_y)| =
          |cov| / Real.sqrt (var_x * var_y) := by
        simp [abs_div, Real.abs_of_nonneg (le_of_lt hden_pos)]
      have habs_le : |cov / Real.sqrt (var_x * var_y)| ≤ 1 := by
        simpa [habs_eq] using hbound_div
      simpa [pearson_correlation, hxy, hvar, cov] using habs_le
  · simp [pearson_correlation, hxy]

/-- Correlation is bounded between -1 and 1. -/
lemma correlation_bounded (x y : List ℝ) :
    -1 ≤ pearson_correlation x y ∧ pearson_correlation x y ≤ 1 := by
  simpa using abs_le.mp (by simpa using pearson_correlation_abs_le_one x y)

/-- A nonempty list is perfectly correlated with itself. -/
lemma pearson_correlation_self_one (x : List ℝ) (hx : 0 < x.length) :
    pearson_correlation x x = 1 := by
  classical
  unfold pearson_correlation
  have hxy : x.length = x.length ∧ 0 < x.length := ⟨rfl, hx⟩
  have hx_nonneg : 0 ≤ Stats.variance x := Stats.variance_nonneg x
  simp [hxy, Stats.covariance_self, hx_nonneg, mul_comm, mul_left_comm, mul_assoc,
    Real.sqrt_mul hx_nonneg hx_nonneg]

/-- Backwards-compatible alias for the self-correlation lemma. -/
lemma perfect_correlation_is_one (x : List ℝ) (hx : 0 < x.length) :
    pearson_correlation x x = 1 :=
  pearson_correlation_self_one x hx

/-! ## Circular Variance (Phase Coherence) -/

/-- Mean resultant length (phase coherence measure) -/
noncomputable def mean_resultant_length (phases : List ℝ) : ℝ :=
  if phases.length > 0 then
    let n := phases.length
    let mean_cos := (phases.map Real.cos).sum / n
    let mean_sin := (phases.map Real.sin).sum / n
    Real.sqrt (mean_cos^2 + mean_sin^2)
  else
    0

/-- Circular variance: V = 1 - R (where R is mean resultant length) -/
noncomputable def circular_variance (phases : List ℝ) : ℝ :=
  1 - mean_resultant_length phases

/--- Circular variance is bounded: 0 ≤ V ≤ 1.
    Proof: Let n = |phases|. If n = 0 then V = 1. If n > 0, set
    C = (∑ cos θᵢ)/n and S = (∑ sin θᵢ)/n. By Cauchy–Schwarz on
    Fin n with the all-ones vector, we have C² ≤ (∑ cos² θᵢ)/n and
    S² ≤ (∑ sin² θᵢ)/n. Adding yields C²+S² ≤ (∑ (cos²+sin²) θᵢ)/n = 1.
    Hence R = √(C²+S²) ∈ [0,1] and V = 1 − R ∈ [0,1]. -/
lemma circular_variance_bounded (phases : List ℝ) :
  0 ≤ circular_variance phases ∧ circular_variance phases ≤ 1 := by
  classical
  unfold circular_variance mean_resultant_length
  by_cases hlen : phases.length > 0
  · -- Nonempty case: prove 0 ≤ 1 - R ≤ 1 via 0 ≤ R ≤ 1
    have hn_pos : 0 < (phases.length : ℝ) := by
      exact_mod_cast hlen
    set n : ℕ := phases.length
    have hn : n = phases.length := rfl
    -- Define sequences over Fin n
    let c : Fin n → ℝ := fun i => Real.cos (phases.get i)
    let s : Fin n → ℝ := fun i => Real.sin (phases.get i)
    let one : Fin n → ℝ := fun _ => (1 : ℝ)
    -- Bounds: |⟪c,1⟫| ≤ ‖c‖‖1‖ and |⟪s,1⟫| ≤ ‖s‖‖1‖
    have hCauchy_c := abs_real_inner_le_norm c one
    have hCauchy_s := abs_real_inner_le_norm s one
    -- Rewrite inner products and norms into sums
    have hsum_c : Real.inner c one = ∑ i : Fin n, c i := by
      simp [Real.inner]  -- scalar product on (Fin n → ℝ)
    have hsum_s : Real.inner s one = ∑ i : Fin n, s i := by
      simp [Real.inner]
    have hnorm1_sq : ‖one‖ ^ 2 = (n : ℝ) := by
      -- ‖1‖² = ∑ 1^2 = n
      have : Real.inner one one = ∑ _i : Fin n, (1 : ℝ) := by
        simp [Real.inner]
      simpa [Real.norm_sq_eq_inner] using this
    have hnorm1 : 0 ≤ ‖one‖ := norm_nonneg _
    -- (∑ cos)^2 ≤ n * ∑ cos^2 and (∑ sin)^2 ≤ n * ∑ sin^2
    have hsum_c_sq : (∑ i : Fin n, c i)^2 ≤ (n : ℝ) * (∑ i : Fin n, (c i)^2) := by
      -- From |⟪c,1⟫| ≤ ‖c‖‖1‖, square both sides
      have h1 : |Real.inner c one| ≤ ‖c‖ * ‖one‖ := hCauchy_c
      have hnonneg : 0 ≤ ‖c‖ * ‖one‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
      have := pow_le_pow_of_le_left (abs_nonneg _) h1 2
      -- Expand: |⟪c,1⟫|^2 ≤ ‖c‖^2 ‖1‖^2
      have := by
        have := abs_real_inner_le_norm c one
        have h := mul_le_mul_of_nonneg_left this (norm_nonneg _)
        exact this
      -- Rewrite explicitly
      have hc : (Real.inner c one)^2 ≤ (‖c‖ * ‖one‖)^2 := by
        exact sq_le_sq.mpr h1
      -- Now substitute definitions
      have hcnorm : ‖c‖ ^ 2 = ∑ i : Fin n, (c i) ^ 2 := by
        have := (Real.norm_sq_eq_inner c)
        have hinner : Real.inner c c = ∑ i : Fin n, (c i) * (c i) := by
          simp [Real.inner]
        simpa [hinner, sq] using this
      have h1norm : ‖one‖ ^ 2 = (n : ℝ) := hnorm1_sq
      simpa [hsum_c, sq, hcnorm, h1norm, mul_comm, mul_left_comm, mul_assoc]
        using hc
    have hsum_s_sq : (∑ i : Fin n, s i)^2 ≤ (n : ℝ) * (∑ i : Fin n, (s i)^2) := by
      have h1 : |Real.inner s one| ≤ ‖s‖ * ‖one‖ := hCauchy_s
      have hc : (Real.inner s one)^2 ≤ (‖s‖ * ‖one‖)^2 := by
        exact sq_le_sq.mpr h1
      have hsnorm : ‖s‖ ^ 2 = ∑ i : Fin n, (s i) ^ 2 := by
        have := (Real.norm_sq_eq_inner s)
        have hinner : Real.inner s s = ∑ i : Fin n, (s i) * (s i) := by
          simp [Real.inner]
        simpa [hinner, sq] using this
      have h1norm : ‖one‖ ^ 2 = (n : ℝ) := hnorm1_sq
      simpa [hsum_s, sq, hsnorm, h1norm, mul_comm, mul_left_comm, mul_assoc]
        using hc
    -- Divide both inequalities by n^2 (positive) to get bounds on means
    have hmean_c : ((∑ i, c i) / (n : ℝ))^2 ≤ (∑ i, (c i)^2) / (n : ℝ) := by
      have hn2_pos : 0 < ((n : ℝ) ^ 2) := by
        have : 0 < (n : ℝ) := hn_pos
        exact pow_pos this 2
      have := (div_le_iff_of_pos (by simpa using hn2_pos)).mpr hsum_c_sq
      -- (∑ c)^2 / n^2 ≤ (n * ∑ c^2) / n^2 = (∑ c^2) / n
      have : (∑ i : Fin n, c i)^2 / (n : ℝ) ^ 2 ≤ (∑ i : Fin n, (c i)^2) / (n : ℝ) := by
        simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv, pow_two]
          using this
      simpa [div_eq_mul_inv, pow_two] using this
    have hmean_s : ((∑ i, s i) / (n : ℝ))^2 ≤ (∑ i, (s i)^2) / (n : ℝ) := by
      have hn2_pos : 0 < ((n : ℝ) ^ 2) := by
        have : 0 < (n : ℝ) := hn_pos
        exact pow_pos this 2
      have := (div_le_iff_of_pos (by simpa using hn2_pos)).mpr hsum_s_sq
      have : (∑ i : Fin n, s i)^2 / (n : ℝ) ^ 2 ≤ (∑ i : Fin n, (s i)^2) / (n : ℝ) := by
        simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv, pow_two]
          using this
      simpa [div_eq_mul_inv, pow_two] using this
    -- Sum bounds and use cos²+sin²=1 pointwise
    have hsum_trig :
        (∑ i : Fin n, (c i)^2) + (∑ i : Fin n, (s i)^2)
          = (n : ℝ) := by
      have : ∀ i : Fin n, (c i)^2 + (s i)^2 = 1 := by
        intro i; simp [c, s, sq, Real.cos_sq_add_sin_sq]
      have := Finset.sum_congr rfl (fun i _ => by simpa using this i)
      have hleft : ∑ i : Fin n, ((c i)^2 + (s i)^2)
          = (∑ i : Fin n, (c i)^2) + (∑ i : Fin n, (s i)^2) := by
        simpa [Finset.sum_add_distrib]
      have hright : ∑ _i : Fin n, (1 : ℝ) = (n : ℝ) := by
        simp
      simpa [hleft] using hright
    have hinside_le_one :
        ((∑ i, c i) / (n : ℝ))^2 + ((∑ i, s i) / (n : ℝ))^2 ≤ 1 := by
      have := add_le_add hmean_c hmean_s
      -- RHS becomes (∑(c^2)+∑(s^2))/n = 1
      have : (∑ i : Fin n, (c i)^2) / (n : ℝ)
            + (∑ i : Fin n, (s i)^2) / (n : ℝ) = 1 := by
        have := by
          have := hsum_trig
          simpa [add_comm, add_left_comm, add_assoc, div_eq_mul_inv]
            using (congrArg (fun t => t / (n : ℝ)) this)
        simpa [add_comm, add_left_comm, add_assoc] using this
      -- Monotonicity of addition gives the desired inequality
      simpa [this]
        using this
    -- Now 0 ≤ R ≤ 1 ⇒ 0 ≤ 1 - R ≤ 1
    have hR_nonneg : 0 ≤ Real.sqrt (((∑ i, c i) / (n : ℝ))^2 + ((∑ i, s i) / (n : ℝ))^2) :=
      Real.sqrt_nonneg _
    have hR_le_one :
        Real.sqrt (((∑ i, c i) / (n : ℝ))^2 + ((∑ i, s i) / (n : ℝ))^2) ≤ 1 := by
      exact Real.sqrt_le'.mpr ⟨by
        have : 0 ≤ ((∑ i, c i) / (n : ℝ))^2 + ((∑ i, s i) / (n : ℝ))^2 := by
          nlinarith
        exact this
        , hinside_le_one⟩
    constructor
    · -- 0 ≤ 1 - R
      have : 0 ≤ 1 - Real.sqrt (((∑ i, c i) / (n : ℝ))^2 + ((∑ i, s i) / (n : ℝ))^2) := by
        have : Real.sqrt (((∑ i, c i) / (n : ℝ))^2 + ((∑ i, s i) / (n : ℝ))^2) ≤ 1 := hR_le_one
        have := sub_nonneg.mpr this
        simpa using this
      simpa [hn, if_pos hlen] using this
    · -- 1 - R ≤ 1
      have : 1 - Real.sqrt (((∑ i, c i) / (n : ℝ))^2 + ((∑ i, s i) / (n : ℝ))^2) ≤ 1 := by
        have hRnn := hR_nonneg
        have := sub_le_self_iff.mpr hR_nonneg
        -- Use: 1 - r ≤ 1 for r ≥ 0
        have : -(Real.sqrt (((∑ i, c i) / (n : ℝ))^2 + ((∑ i, s i) / (n : ℝ))^2)) ≤ 0 := by
          simpa using (neg_nonpos.mpr hR_nonneg)
        have := add_le_add_left this 1
        simpa [sub_eq_add_neg] using this
      simpa [hn, if_pos hlen] using this

/--- Perfect phase coherence gives V = 0.
    All phases equal θ ⇒ mean cos = cos θ and mean sin = sin θ ⇒ R = 1. -/
lemma perfect_coherence_is_zero (phase : ℝ) (n : ℕ) (h : 0 < n) :
  circular_variance (List.replicate n phase) = 0 := by
  classical
  unfold circular_variance mean_resultant_length
  have hlen : (List.replicate n phase).length > 0 := by
    simpa using h
  simp [hlen]
  -- compute means for constant list
  have hsum_cos : (List.map Real.cos (List.replicate n phase)).sum = (n : ℝ) * Real.cos phase := by
    simp [List.map_replicate, List.sum_replicate]
  have hsum_sin : (List.map Real.sin (List.replicate n phase)).sum = (n : ℝ) * Real.sin phase := by
    simp [List.map_replicate, List.sum_replicate]
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt h)
  have hmean_cos : (List.map Real.cos (List.replicate n phase)).sum / n = Real.cos phase := by
    field_simp [hsum_cos, hn_ne]
  have hmean_sin : (List.map Real.sin (List.replicate n phase)).sum / n = Real.sin phase := by
    field_simp [hsum_sin, hn_ne]
  simp [hmean_cos, hmean_sin, sq, Real.cos_sq_add_sin_sq]

/--- Complete decoherence gives V = 1 when R = 0. -/
lemma complete_decoherence_is_one :
  ∀ (phases : List ℝ),
    (mean_resultant_length phases = 0) →
    circular_variance phases = 1 := by
  intro phases hR
  unfold circular_variance
  simp [mean_resultant_length, hR]

/-- Acceptance: circular variance threshold -/
def meets_phase_coherence_threshold (cv : ℝ) (threshold : ℝ) : Prop :=
  cv ≤ threshold

/-! ## Tolerance-Aware BIOPHASE Checks -/

/-- Wavenumber center within tolerance (cm⁻¹). -/
def meets_band_center_tolerance
  (nu_measured_cm1 nu0_cm1 : ℝ)
  (tol : IndisputableMonolith.BiophaseCore.Tolerances) : Prop :=
  |nu_measured_cm1 - nu0_cm1| ≤ tol.delta_nu_cm1

/-- Wavelength within tolerance (μm). -/
def meets_wavelength_tolerance
  (lambda_measured_um lambda0_um : ℝ)
  (tol : IndisputableMonolith.BiophaseCore.Tolerances) : Prop :=
  |lambda_measured_um - lambda0_um| ≤ tol.delta_lambda_um

/-- Timing jitter within tolerance (ps). -/
def meets_timing_jitter
  (observed_jitter_ps : ℝ)
  (tol : IndisputableMonolith.BiophaseCore.Tolerances) : Prop :=
  observed_jitter_ps ≤ tol.timing_jitter_ps

/-! ## Combined Acceptance -/

/-- A signal meets all three BIOPHASE acceptance criteria -/
structure MeetsAcceptance where
  /-- Correlation value -/
  rho : ℝ
  /-- SNR value -/
  snr : ℝ
  /-- Circular variance value -/
  circ_var : ℝ

  /-- Correlation threshold -/
  rho_threshold : ℝ
  /-- SNR threshold -/
  snr_threshold : ℝ
  /-- Circular variance threshold -/
  cv_threshold : ℝ

  /-- Correlation meets threshold -/
  rho_ok : rho ≥ rho_threshold
  /-- SNR meets threshold -/
  snr_ok : snr ≥ snr_threshold
  /-- Phase coherence meets threshold -/
  cv_ok : circ_var ≤ cv_threshold


/-- Standard BIOPHASE acceptance witness. -/
def standard_acceptance (rho snr cv : ℝ)
    (h_rho : rho ≥ 0.30) (h_snr : snr ≥ 5.0) (h_cv : cv ≤ 0.40) :
    MeetsAcceptance := {
  rho := rho
  snr := snr
  circ_var := cv
  rho_threshold := 0.30
  snr_threshold := 5.0
  cv_threshold := 0.40
  rho_ok := h_rho
  snr_ok := h_snr
  cv_ok := h_cv
}

 /-- Predicate: values meet standard BIOPHASE acceptance -/
def passes_standard_acceptance (rho snr cv : ℝ) : Prop :=
  rho ≥ 0.30 ∧ snr ≥ 5.0 ∧ cv ≤ 0.40

/-- Aggregated metrics derived from spectral observations. -/
structure AcceptanceSnapshot where
  /-- Average band center in cm⁻¹. -/
  wavenumber_cm1 : ℝ
  /-- Average wavelength in μm. -/
  wavelength_um : ℝ
  /-- Pearson correlation coefficient. -/
  rho : ℝ
  /-- Signal-to-noise ratio (RMS-based). -/
  snr : ℝ
  /-- Circular variance of phase samples. -/
  circular_variance : ℝ
  /-- Timing jitter envelope (ps). -/
  timing_jitter_ps : ℝ
deriving Repr

namespace AcceptanceSnapshot

open DataIO
open Stats

/-- Construct a snapshot from raw observations with respect to a BIOPHASE spec. -/
noncomputable def fromObservation
    (spec : BiophaseCore.BiophaseSpecFull) (obs : DataIO.RealObservation) : AcceptanceSnapshot :=
  let nuAvg? := optionalMean obs.wavenumbers_cm1
  let lambdaAvg? := optionalMean obs.wavelengths_um
  let nuMeasured : ℝ :=
    match nuAvg?, lambdaAvg? with
    | some ν, _ => ν
    | none, some λμm =>
        let λm := λμm * 1e-6
        BiophaseCore.lambda_to_nu_cm1 λm
    | none, none => spec.nu0_cm1
  let lambdaMeasured : ℝ :=
    match lambdaAvg?, nuAvg? with
    | some λμm, _ => λμm
    | none, some νcm1 =>
        (BiophaseCore.nu_cm1_to_lambda νcm1) * 1e6
    | none, none => spec.lambda0
  let signal := obs.signal
  let reference := obs.reference
  let phases := obs.phases
  let rho := pearson_correlation signal reference
  let snr := signalToNoiseRatio signal reference
  let cv := circular_variance phases
  {
    wavenumber_cm1 := nuMeasured
    wavelength_um := lambdaMeasured
    rho := rho
    snr := snr
    circular_variance := cv
    timing_jitter_ps := obs.timing_jitter_ps
  }

/-- Determine falsifiers triggered by the snapshot under tolerances. -/
def activeFalsifiers
    (spec : BiophaseCore.BiophaseSpecFull)
    (tol : BiophaseCore.Tolerances)
    (snapshot : AcceptanceSnapshot) : List (String × String) :=
  let base : List (String × String) := []
  let base :=
    if meets_band_center_tolerance snapshot.wavenumber_cm1 spec.nu0_cm1 tol then base
    else ("BandCenterOutOfTolerance",
          s!"|Δν| = {abs (snapshot.wavenumber_cm1 - spec.nu0_cm1)} > {tol.delta_nu_cm1}") :: base
  let base :=
    if meets_wavelength_tolerance snapshot.wavelength_um spec.lambda0 tol then base
    else ("WavelengthOutOfTolerance",
          s!"|Δλ| = {abs (snapshot.wavelength_um - spec.lambda0)} > {tol.delta_lambda_um}") :: base
  let base :=
    if meets_timing_jitter snapshot.timing_jitter_ps tol then base
    else ("TimingJitterExceeded",
          s!"τ_jitter = {snapshot.timing_jitter_ps} ps > {tol.timing_jitter_ps} ps") :: base
  let base :=
    if snapshot.rho ≥ spec.rho_min then base
    else ("CorrelationBelowThreshold",
          s!"ρ = {snapshot.rho} < {spec.rho_min}") :: base
  let base :=
    if snapshot.snr ≥ spec.snr_min then base
    else ("SNRBelowThreshold",
          s!"SNR = {snapshot.snr} < {spec.snr_min}") :: base
  let base :=
    if snapshot.circular_variance ≤ spec.circ_var_max then base
    else ("CircularVarianceAboveThreshold",
          s!"V = {snapshot.circular_variance} > {spec.circ_var_max}") :: base
  base.reverse

/-- JSON summary for an acceptance snapshot. -/
def summaryJson
    (spec : BiophaseCore.BiophaseSpecFull)
    (tol : BiophaseCore.Tolerances)
    (snapshot : AcceptanceSnapshot) : Json :=
  let toleranceJson := Json.mkObj [
    ("delta_lambda_um", jsonOfReal tol.delta_lambda_um),
    ("delta_nu_cm1", jsonOfReal tol.delta_nu_cm1),
    ("timing_jitter_ps", jsonOfReal tol.timing_jitter_ps)
  ]
  let thresholdsJson := Json.mkObj [
    ("rho_min", jsonOfReal spec.rho_min),
    ("snr_min", jsonOfReal spec.snr_min),
    ("circ_var_max", jsonOfReal spec.circ_var_max)
  ]
  let passes := passes_standard_acceptance snapshot.rho snapshot.snr snapshot.circular_variance
  let checks := Json.mkObj [
    ("band_center_ok", Json.bool (meets_band_center_tolerance snapshot.wavenumber_cm1 spec.nu0_cm1 tol)),
    ("wavelength_ok", Json.bool (meets_wavelength_tolerance snapshot.wavelength_um spec.lambda0 tol)),
    ("timing_ok", Json.bool (meets_timing_jitter snapshot.timing_jitter_ps tol)),
    ("correlation_ok", Json.bool (snapshot.rho ≥ spec.rho_min)),
    ("snr_ok", Json.bool (snapshot.snr ≥ spec.snr_min)),
    ("circular_variance_ok", Json.bool (snapshot.circular_variance ≤ spec.circ_var_max))
  ]
  let falsifiers := activeFalsifiers spec tol snapshot
  let falsifiersJson := Json.arr <|
    Array.mk <|
      falsifiers.map fun (name, reason) =>
        Json.mkObj [("predicate", Json.str name), ("reason", Json.str reason)]
  Json.mkObj [
    ("wavenumber_cm1", jsonOfReal snapshot.wavenumber_cm1),
    ("wavelength_um", jsonOfReal snapshot.wavelength_um),
    ("rho", jsonOfReal snapshot.rho),
    ("snr", jsonOfReal snapshot.snr),
    ("circular_variance", jsonOfReal snapshot.circular_variance),
    ("timing_jitter_ps", jsonOfReal snapshot.timing_jitter_ps),
    ("tolerances", toleranceJson),
    ("thresholds", thresholdsJson),
    ("passes_standard_acceptance", Json.bool passes),
    ("checks", checks),
    ("active_falsifiers", falsifiersJson)
  ]

end AcceptanceSnapshot

/-! ## Examples and Tests -/

/-- Example: High-quality EM signal passes -/
example : passes_standard_acceptance 0.85 25.0 0.15 := by
  unfold passes_standard_acceptance
  norm_num

/-- Example: Low SNR fails -/
example : ¬passes_standard_acceptance 0.85 2.0 0.15 := by
  unfold passes_standard_acceptance
  norm_num

/-- Example: Poor coherence fails -/
example : ¬passes_standard_acceptance 0.85 25.0 0.60 := by
  unfold passes_standard_acceptance
  norm_num

end BiophaseIntegration
end IndisputableMonolith
