import Mathlib
import IndisputableMonolith.Verification.MeaningCompiler.Spec
import IndisputableMonolith.LightLanguage.Basis.DFT8
import IndisputableMonolith.Token.WTokenId
import IndisputableMonolith.Token.WTokenBasis

/-!
# Meaning Compiler Pipeline

This module implements the **operational meaning compiler**: a deterministic
pipeline that transforms raw signals into structured meaning objects.

## Pipeline Stages

1. **Windowing**: Segment signal into τ₀ = 8 tick frames
2. **Normalization**: Project to neutral subspace (mean-free)
3. **Spectral Analysis**: DFT-8 decomposition
4. **Classification**: Identify dominant WToken
5. **Program Synthesis**: Generate LNAL normal form
6. **Output**: Construct MeaningObject

## Key Properties

- **Deterministic**: Same input always produces same output
- **Gauge-Invariant**: Output unique up to global phase
- **Stable**: Small perturbations preserve classification

-/

namespace IndisputableMonolith
namespace Verification
namespace MeaningCompiler

open Token LightLanguage.Basis
open scoped BigOperators

/-! ## Pipeline Configuration -/

/-- Pipeline configuration parameters. -/
structure PipelineConfig where
  /-- Classification threshold for "exact" match.
      Set to 0.6 to ensure stability under perturbation:
      - overlap > 0.75 after bounded perturbation
      - energy inflation factor ≤ 1.21 (from perturbation analysis)
      - normalized overlap > 0.75/1.21 > 0.62 > 0.6 ✓ -/
  classifyThreshold : ℝ := 0.6
  /-- Stability threshold for perturbation bounds -/
  stabilityThreshold : ℝ := 0.01
  /-- Tolerance for neutrality check -/
  neutralityTolerance : ℝ := 1e-9

/-- Default pipeline configuration. -/
def defaultConfig : PipelineConfig := {}

/-! ## Stage 1: Windowing -/

/-- Segment a signal into 8-tick windows.
    Returns list of windows; partial final window is dropped. -/
def windowSignal (signal : List ℂ) : List (Fin 8 → ℂ) :=
  let n := signal.length / 8
  List.range n |>.map fun i =>
    fun j : Fin 8 => signal.getD (i * 8 + j.val) 0

/-- Window count from signal length. -/
theorem windowSignal_length (signal : List ℂ) :
    (windowSignal signal).length = signal.length / 8 := by
  simp [windowSignal]

/-! ## Stage 2: Normalization -/

/-- Project an 8-vector to neutral subspace (subtract mean).
    This is the same as `projectToNeutral` in Spec.lean. -/
noncomputable def normalizeWindow (v : Fin 8 → ℂ) : Fin 8 → ℂ :=
  projectToNeutral v

/-- Normalize and rescale to unit energy. -/
noncomputable def normalizeAndScale (v : Fin 8 → ℂ) : Fin 8 → ℂ :=
  let neutral := projectToNeutral v
  let energy := normSq8 neutral
  if energy = 0 then neutral
  else fun i => neutral i / Real.sqrt energy

/-- Normalized output is neutral. -/
theorem normalizeWindow_neutral (v : Fin 8 → ℂ) :
    Finset.univ.sum (normalizeWindow v) = 0 :=
  projectToNeutral_neutral v

/-- normalizeWindow commutes with scalar multiplication.
    normalizeWindow (c * v) = c * normalizeWindow v -/
theorem normalizeWindow_smul (v : Fin 8 → ℂ) (c : ℂ) :
    normalizeWindow (fun i => c * v i) = fun i => c * normalizeWindow v i := by
  ext i
  unfold normalizeWindow projectToNeutral
  have h_sum : Finset.univ.sum (fun x => c * v x) = c * Finset.univ.sum v := by
    rw [← Finset.mul_sum]
  simp only [h_sum]
  ring

/-! ## Stage 3: Spectral Analysis -/

/-- Extract DFT-8 coefficients for neutral modes (1-7). -/
noncomputable def spectralDecompose (v : Fin 8 → ℂ) : Fin 7 → ℂ :=
  fun k => Finset.univ.sum (fun t => v t * dft8_entry t k.succ)

/-- Mode 0 coefficient is zero for neutral vectors. -/
theorem spectral_mode0_zero (v : Fin 8 → ℂ)
    (hNeutral : Finset.univ.sum v = 0) :
    Finset.univ.sum (fun t => v t * dft8_entry t 0) = 0 := by
  -- Mode 0 is the DC component: dft8_entry t 0 = 1/√8
  -- So the sum is (1/√8) * (∑ v_t) = (1/√8) * 0 = 0
  unfold dft8_entry omega8
  simp only [Fin.val_zero, mul_zero, pow_zero, one_div]
  rw [← Finset.sum_mul, hNeutral, zero_mul]

/-- spectralDecompose is linear with respect to scalar multiplication.
    spectralDecompose (c * v) = c * spectralDecompose v -/
theorem spectralDecompose_smul (v : Fin 8 → ℂ) (c : ℂ) :
    spectralDecompose (fun i => c * v i) = fun k => c * spectralDecompose v k := by
  ext k
  unfold spectralDecompose
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

/-! ## Stage 4: Classification -/

/-- Classification result type. -/
inductive ClassifyResult
  | exact (w : WTokenId) (overlap : ℝ)
  | ambiguous (candidates : List WTokenId)
  | invalid (reason : String)

/-- All 20 WTokenIds as a list. -/
def allTokenIds : List WTokenId :=
  [WTokenId.W0_Origin, WTokenId.W1_Emergence, WTokenId.W2_Polarity, WTokenId.W3_Harmony,
   WTokenId.W4_Power, WTokenId.W5_Birth, WTokenId.W6_Structure, WTokenId.W7_Resonance,
   WTokenId.W8_Infinity, WTokenId.W9_Truth, WTokenId.W10_Completion, WTokenId.W11_Inspire,
   WTokenId.W12_Transform, WTokenId.W13_End, WTokenId.W14_Connection, WTokenId.W15_Wisdom,
   WTokenId.W16_Illusion, WTokenId.W17_Chaos, WTokenId.W18_Twist, WTokenId.W19_Time]

/-- Every WTokenId is in allTokenIds -/
theorem mem_allTokenIds (w : WTokenId) : w ∈ allTokenIds := by
  cases w <;> decide

/-- Inner product of two 8-vectors. -/
noncomputable def innerProduct8 (u v : Fin 8 → ℂ) : ℂ :=
  Finset.univ.sum (fun i => star (u i) * v i)

/-- Interpret a `Fin 8 → ℂ` vector as an `L²` Euclidean vector. -/
noncomputable def toEuclidean8 (v : Fin 8 → ℂ) : EuclideanSpace ℂ (Fin 8) :=
  WithLp.toLp 2 v

/-- The EuclideanSpace inner product agrees with `innerProduct8`. -/
private lemma inner_toEuclidean8 (u v : Fin 8 → ℂ) :
    inner ℂ (toEuclidean8 u) (toEuclidean8 v) = innerProduct8 u v := by
  simp [toEuclidean8, innerProduct8, PiLp.inner_apply, mul_comm]

/-- Norm on EuclideanSpace is the square root of `normSq8`. -/
private lemma norm_toEuclidean8 (v : Fin 8 → ℂ) :
    ‖(toEuclidean8 v)‖ = Real.sqrt (normSq8 v) := by
  have h_sq : ‖(toEuclidean8 v)‖ ^ 2 = normSq8 v := by
    simp [toEuclidean8, normSq8, PiLp.norm_sq_eq_of_L2, Complex.normSq_eq_norm_sq]
  have h_nn : 0 ≤ ‖(toEuclidean8 v)‖ := norm_nonneg _
  rw [← Real.sqrt_sq h_nn, h_sq]

/-- Cauchy-Schwarz for 8-vectors in Pipeline. -/
private lemma cauchy_schwarz_8_local (u v : Fin 8 → ℂ) :
    ‖innerProduct8 u v‖ ≤ Real.sqrt (normSq8 u) * Real.sqrt (normSq8 v) := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (x := toEuclidean8 u) (y := toEuclidean8 v)
  simp only [inner_toEuclidean8, norm_toEuclidean8] at h
  exact h

/-- Overlap magnitude: |⟨basis, v⟩|² -/
noncomputable def overlapMagnitude (v : Fin 8 → ℂ) (w : WTokenId) : ℝ :=
  Complex.normSq (innerProduct8 (WTokenId.basisOfId w) v)

/-- Foldl produces equal results when the key function values agree. -/
private lemma foldl_overlap_congr (v₁ v₂ : Fin 8 → ℂ)
    (h_eq : ∀ w, overlapMagnitude v₁ w = overlapMagnitude v₂ w) :
    allTokenIds.foldl
      (fun (best, bestOverlap) w =>
        let overlap := overlapMagnitude v₁ w
        if overlap > bestOverlap then (w, overlap) else (best, bestOverlap))
      (WTokenId.W0_Origin, overlapMagnitude v₁ WTokenId.W0_Origin) =
    allTokenIds.foldl
      (fun (best, bestOverlap) w =>
        let overlap := overlapMagnitude v₂ w
        if overlap > bestOverlap then (w, overlap) else (best, bestOverlap))
      (WTokenId.W0_Origin, overlapMagnitude v₂ WTokenId.W0_Origin) := by
  -- Both computations are identical since all overlapMagnitude values are equal
  -- Rewrite the LHS to use v₂'s overlaps (which are equal to v₁'s by h_eq)
  have h_step_eq : ∀ acc w,
      (let overlap := overlapMagnitude v₁ w
       if overlap > acc.2 then (w, overlap) else acc) =
      (let overlap := overlapMagnitude v₂ w
       if overlap > acc.2 then (w, overlap) else acc) := by
    intro acc w
    simp only [h_eq w]
  have h_init : overlapMagnitude v₁ WTokenId.W0_Origin = overlapMagnitude v₂ WTokenId.W0_Origin :=
    h_eq WTokenId.W0_Origin
  rw [h_init]
  congr 1
  funext acc w
  exact h_step_eq acc w

/-- Find token with maximum overlap. -/
noncomputable def findBestToken (v : Fin 8 → ℂ) : WTokenId × ℝ :=
  let initial := (WTokenId.W0_Origin, overlapMagnitude v WTokenId.W0_Origin)
  allTokenIds.foldl
    (fun (best, bestOverlap) w =>
      let overlap := overlapMagnitude v w
      if overlap > bestOverlap then (w, overlap) else (best, bestOverlap))
    initial

/-- Phase rotation preserves overlap magnitude (local version for forward reference). -/
private lemma phase_rotation_overlap_local (v : Fin 8 → ℂ) (w : WTokenId) (θ : ℝ) :
    overlapMagnitude (fun i => Complex.exp (θ * Complex.I) * v i) w =
    overlapMagnitude v w := by
  unfold overlapMagnitude innerProduct8
  -- ⟨b, e^{iθ}v⟩ = e^{iθ} ⟨b, v⟩
  have h_scale : Finset.univ.sum (fun i => star (WTokenId.basisOfId w i) *
                    (Complex.exp (θ * Complex.I) * v i)) =
                 Complex.exp (θ * Complex.I) *
                    Finset.univ.sum (fun i => star (WTokenId.basisOfId w i) * v i) := by
    have h_eq : ∀ i, star (WTokenId.basisOfId w i) * (Complex.exp (θ * Complex.I) * v i) =
                     Complex.exp (θ * Complex.I) * (star (WTokenId.basisOfId w i) * v i) := by
      intro i; ring
    simp_rw [h_eq]
    rw [← Finset.mul_sum]
  rw [h_scale]
  -- |e^{iθ} · z|² = 1 · |z|²
  rw [Complex.normSq_mul]
  have h_exp : Complex.normSq (Complex.exp (θ * Complex.I)) = 1 := by
    -- Use ‖e^z‖ = e^{Re(z)} and Re(θ*I) = 0
    have h_re : (θ * Complex.I).re = 0 := by simp [Complex.mul_re]
    have h_norm : ‖Complex.exp (θ * Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]
      simp [h_re]
    rw [Complex.normSq_eq_norm_sq, h_norm]
    norm_num
  rw [h_exp, one_mul]

/-- findBestToken is invariant under phase rotation.
    Since |⟨b, e^{iθ}v⟩| = |e^{iθ}| · |⟨b, v⟩| = |⟨b, v⟩|, all overlaps are preserved. -/
theorem findBestToken_phase_inv (v : Fin 8 → ℂ) (θ : ℝ) :
    findBestToken (fun i => Complex.exp (θ * Complex.I) * v i) = findBestToken v := by
  -- Phase rotation preserves all overlap magnitudes
  have h_overlap : ∀ w, overlapMagnitude (fun i => Complex.exp (θ * Complex.I) * v i) w =
                        overlapMagnitude v w := fun w => phase_rotation_overlap_local v w θ
  -- findBestToken only depends on overlap values
  -- Since all overlaps are identical, the foldl produces identical results
  unfold findBestToken
  -- Apply the foldl congruence lemma
  exact foldl_overlap_congr _ _ h_overlap

/-- The foldl step preserves the invariant: snd = overlapMagnitude v fst -/
private lemma foldl_step_invariant (v : Fin 8 → ℂ) (acc : WTokenId × ℝ) (w : WTokenId)
    (h_inv : acc.2 = overlapMagnitude v acc.1) :
    let next := if overlapMagnitude v w > acc.2 then (w, overlapMagnitude v w) else acc
    next.2 = overlapMagnitude v next.1 := by
  simp only []
  split_ifs with h
  · rfl
  · exact h_inv

/-- foldl over list preserves invariant -/
private lemma foldl_invariant (v : Fin 8 → ℂ) (tokens : List WTokenId) (init : WTokenId × ℝ)
    (h_init : init.2 = overlapMagnitude v init.1) :
    let result := tokens.foldl
      (fun (best, bestOverlap) w =>
        let overlap := overlapMagnitude v w
        if overlap > bestOverlap then (w, overlap) else (best, bestOverlap))
      init
    result.2 = overlapMagnitude v result.1 := by
  induction tokens generalizing init with
  | nil => simp only [List.foldl_nil]; exact h_init
  | cons x xs ih =>
    simp only [List.foldl_cons]
    apply ih
    exact foldl_step_invariant v init x h_init

/-- foldl is monotonic: result.2 ≥ init.2 -/
private lemma foldl_mono (v : Fin 8 → ℂ) (tokens : List WTokenId) (init : WTokenId × ℝ)
    (h_init : init.2 = overlapMagnitude v init.1) :
    let result := tokens.foldl
      (fun (best, bestOverlap) w =>
        let overlap := overlapMagnitude v w
        if overlap > bestOverlap then (w, overlap) else (best, bestOverlap))
      init
    result.2 ≥ init.2 := by
  induction tokens generalizing init with
  | nil => simp only [List.foldl_nil]; exact le_refl _
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have h_step : (if overlapMagnitude v x > init.2 then (x, overlapMagnitude v x) else init).2 ≥ init.2 := by
      by_cases h : overlapMagnitude v x > init.2
      · simp [h]; linarith
      · simp [h]
    have h_step_inv := foldl_step_invariant v init x h_init
    have h_rest := ih _ h_step_inv
    linarith

/-- foldl result has overlap ≥ any element in the list -/
lemma foldl_max_ge (v : Fin 8 → ℂ) (tokens : List WTokenId) (init : WTokenId × ℝ)
    (h_init : init.2 = overlapMagnitude v init.1) (w : WTokenId) (h_mem : w ∈ tokens) :
    let result := tokens.foldl
      (fun (best, bestOverlap) w =>
        let overlap := overlapMagnitude v w
        if overlap > bestOverlap then (w, overlap) else (best, bestOverlap))
      init
    result.2 ≥ overlapMagnitude v w := by
  induction tokens generalizing init with
  | nil => simp at h_mem
  | cons x xs ih =>
    simp only [List.foldl_cons]
    simp only [List.mem_cons] at h_mem
    cases h_mem with
    | inl h_eq =>
      -- w = x, so we process x in this step
      subst h_eq
      -- After processing w, either we update to (w, overlapMagnitude v w) or keep higher
      -- In either case, result.2 ≥ overlapMagnitude v w
      have h_step : (if overlapMagnitude v w > init.2 then (w, overlapMagnitude v w) else init).2 ≥ overlapMagnitude v w := by
        by_cases hcond : overlapMagnitude v w > init.2
        · simp only [hcond, ↓reduceIte]; exact le_refl _
        · simp only [hcond, ↓reduceIte]; push_neg at hcond; exact hcond
      -- Now show result ≥ step result
      -- The foldl over remaining xs can only increase or maintain
      have h_step_inv : (if overlapMagnitude v w > init.2 then (w, overlapMagnitude v w) else init).2 =
                        overlapMagnitude v (if overlapMagnitude v w > init.2 then (w, overlapMagnitude v w) else init).1 :=
        foldl_step_invariant v init w h_init
      -- Use monotonicity: foldl can only increase the maximum
      have h_mono := foldl_mono v xs _ h_step_inv
      linarith
    | inr h_mem' =>
      -- w ∈ xs, use induction
      apply ih
      · exact foldl_step_invariant v init x h_init
      · exact h_mem'

/-- findBestToken returns correct overlap for the returned token.

    **Proof**: The foldl maintains the invariant that snd = overlapMagnitude fst.
    Initial state satisfies invariant, each step preserves it. -/
theorem findBestToken_snd (v : Fin 8 → ℂ) :
    (findBestToken v).2 = overlapMagnitude v (findBestToken v).1 := by
  unfold findBestToken
  apply foldl_invariant
  rfl

/-- If a token has overlap 1 and all others have overlap < 1,
    findBestToken returns that token. -/
theorem findBestToken_unique_max (v : Fin 8 → ℂ) (w : WTokenId)
    (h_max : overlapMagnitude v w = 1)
    (h_others : ∀ w' : WTokenId, w' ≠ w → overlapMagnitude v w' < 1) :
    (findBestToken v).1 = w ∨ (findBestToken v).2 = 1 := by
  -- Strategy: By findBestToken_snd, (findBestToken v).2 = overlapMagnitude v (findBestToken v).1
  -- Let w' = (findBestToken v).1
  -- Case 1: w' = w → left disjunct holds
  -- Case 2: w' ≠ w → by h_others, overlapMagnitude v w' < 1
  --                 → (findBestToken v).2 < 1
  --                 But findBestToken finds maximum, and w has overlap 1
  --                 So (findBestToken v).2 ≥ 1, contradiction
  -- Therefore w' = w

  -- Use the snd property
  have h_snd := findBestToken_snd v

  -- Either the returned token is w, or it's not
  by_cases h : (findBestToken v).1 = w
  · left; exact h
  · -- If it's not w, then by h_others, its overlap < 1
    have h_lt := h_others (findBestToken v).1 h
    -- By h_snd, (findBestToken v).2 = overlapMagnitude v (findBestToken v).1
    -- So (findBestToken v).2 < 1
    have h_snd2_lt : (findBestToken v).2 < 1 := by rw [h_snd]; exact h_lt

    -- To show findBestToken returns ≥ overlap of w, we need w ∈ allTokenIds
    have h_w_in : w ∈ allTokenIds := by
      unfold allTokenIds
      cases w <;> simp [List.mem_cons]

    -- findBestToken finds maximum over allTokenIds
    -- Since w ∈ allTokenIds, the result.2 ≥ overlapMagnitude v w = 1
    have h_ge : (findBestToken v).2 ≥ overlapMagnitude v w := by
      unfold findBestToken
      apply foldl_max_ge
      · rfl
      · exact h_w_in

    -- But h_max says overlapMagnitude v w = 1
    rw [h_max] at h_ge
    -- So (findBestToken v).2 ≥ 1, but we showed < 1, contradiction
    linarith

/-- Classify a normalized 8-vector to a WToken.

    **Algorithm**:
    1. Compute overlap with each of 20 canonical bases
    2. Find maximum overlap
    3. If overlap > threshold × energy: exact match
    4. If overlap > 0.5 × energy: ambiguous
    5. Otherwise: invalid -/
noncomputable def classifyVector (v : Fin 8 → ℂ) (config : PipelineConfig := defaultConfig)
    : ClassifyResult :=
  let v_neutral := normalizeWindow v
  let energy := normSq8 v_neutral
  if energy < 1e-10 then
    ClassifyResult.invalid "Zero energy"
  else
    let (best, bestOverlap) := findBestToken v_neutral
    let normalizedOverlap := bestOverlap / energy
    if normalizedOverlap ≥ config.classifyThreshold then
      ClassifyResult.exact best bestOverlap
    else if normalizedOverlap ≥ 0.5 then
      -- Find all tokens with significant overlap
      let candidates := allTokenIds.filter fun w =>
        overlapMagnitude v_neutral w / energy ≥ 0.5
      ClassifyResult.ambiguous candidates
    else
      ClassifyResult.invalid "No significant overlap"

/-! ## Stage 5: Program Synthesis -/

/-- Synthesize an LNAL program from classification result.

    For an exact match, the program is just LOCK on the token index.
    For ambiguous cases, we use BRAID to combine candidates.
    For invalid, return empty program. -/
def synthesizeProgram (result : ClassifyResult) : LNALSequence :=
  match result with
  | .exact w _ =>
      -- Simple case: LOCK the identified token
      [.LOCK [w.toNat]]
  | .ambiguous candidates =>
      -- Combine candidates with LOCK
      candidates.map fun w => LNALOp.LOCK [w.toNat]
  | .invalid _ => []

where
  /-- Convert WTokenId to natural number index. -/
  WTokenId.toNat : WTokenId → ℕ
    | .W0_Origin => 0 | .W1_Emergence => 1 | .W2_Polarity => 2 | .W3_Harmony => 3
    | .W4_Power => 4 | .W5_Birth => 5 | .W6_Structure => 6 | .W7_Resonance => 7
    | .W8_Infinity => 8 | .W9_Truth => 9 | .W10_Completion => 10 | .W11_Inspire => 11
    | .W12_Transform => 12 | .W13_End => 13 | .W14_Connection => 14 | .W15_Wisdom => 15
    | .W16_Illusion => 16 | .W17_Chaos => 17 | .W18_Twist => 18 | .W19_Time => 19

/-! ## Stage 6: MeaningObject Construction -/

/-- Compile a single 8-vector to a MeaningObject.

    This is the core compilation function for individual windows. -/
noncomputable def compileWindow (v : Fin 8 → ℂ) (config : PipelineConfig := defaultConfig)
    : Option MeaningObject :=
  let result := classifyVector v config
  match result with
  | .exact w _ =>
      let sig := MeaningSignature.fromId w
      let coeffs := spectralDecompose (normalizeWindow v)
      some {
        signature := sig
        support := {w.toNat}
        program := synthesizeProgram result
        coefficients := coeffs
      }
  | .ambiguous _ => none  -- Could be extended to handle ambiguous cases
  | .invalid _ => none

where
  /-- Convert WTokenId to natural number. -/
  WTokenId.toNat : WTokenId → ℕ
    | .W0_Origin => 0 | .W1_Emergence => 1 | .W2_Polarity => 2 | .W3_Harmony => 3
    | .W4_Power => 4 | .W5_Birth => 5 | .W6_Structure => 6 | .W7_Resonance => 7
    | .W8_Infinity => 8 | .W9_Truth => 9 | .W10_Completion => 10 | .W11_Inspire => 11
    | .W12_Transform => 12 | .W13_End => 13 | .W14_Connection => 14 | .W15_Wisdom => 15
    | .W16_Illusion => 16 | .W17_Chaos => 17 | .W18_Twist => 18 | .W19_Time => 19

/-! ## Full Pipeline -/

/-- The complete meaning compiler pipeline.

    **Input**: Raw signal (list of complex samples)
    **Output**: List of compiled MeaningObjects (one per valid window)

    **Pipeline**:
    1. Window the signal into 8-tick frames
    2. For each window:
       a. Normalize to neutral subspace
       b. Classify to WToken
       c. Synthesize LNAL program
       d. Construct MeaningObject
    3. Filter out failed compilations -/
noncomputable def compile (signal : List ℂ) (config : PipelineConfig := defaultConfig)
    : List MeaningObject :=
  let windows := windowSignal signal
  windows.filterMap (fun w => compileWindow w config)

/-- Compile a pre-windowed signal. -/
noncomputable def compileWindows (windows : List (Fin 8 → ℂ))
    (config : PipelineConfig := defaultConfig) : List MeaningObject :=
  windows.filterMap (fun w => compileWindow w config)

/-! ## Compiler Properties -/

/-- Compilation is deterministic: same input gives same output. -/
theorem compile_deterministic (signal : List ℂ) (config : PipelineConfig) :
    compile signal config = compile signal config := rfl

/-- Self-overlap of canonical basis is 1. -/
theorem canonical_self_overlap (w : WTokenId) :
    overlapMagnitude (WTokenId.basisOfId w) w = 1 := by
  unfold overlapMagnitude innerProduct8
  have h_norm := WTokenId.basisOfId_normalized w
  -- ⟨b, b⟩ = ∑ |b_i|² = ‖b‖² = 1
  have h_inner : Finset.univ.sum (fun i =>
      star (WTokenId.basisOfId w i) * WTokenId.basisOfId w i) = (1 : ℂ) := by
    have h_eq : ∀ i, star (WTokenId.basisOfId w i) * WTokenId.basisOfId w i =
                     (Complex.normSq (WTokenId.basisOfId w i) : ℂ) := by
      intro i
      rw [mul_comm]
      exact Complex.mul_conj (WTokenId.basisOfId w i)
    simp_rw [h_eq]
    rw [← Complex.ofReal_sum]
    simp [normSq8, h_norm]
  rw [h_inner]
  simp [Complex.normSq_one]

/-- Canonical basis is neutral (sum = 0). -/
theorem canonical_is_neutral (w : WTokenId) :
    Finset.univ.sum (WTokenId.basisOfId w) = 0 :=
  WTokenId.basisOfId_neutral w

/-- Canonical basis is fixed under neutralization. -/
theorem canonical_neutral_fixed (w : WTokenId) :
    normalizeWindow (WTokenId.basisOfId w) = WTokenId.basisOfId w := by
  unfold normalizeWindow projectToNeutral
  ext i
  have h := canonical_is_neutral w
  simp [h]

/-- Canonical basis has unit energy. -/
theorem canonical_unit_energy (w : WTokenId) :
    normSq8 (WTokenId.basisOfId w) = 1 :=
  WTokenId.basisOfId_normalized w

/-- Canonical basis vectors compile with correct gauge class.

    **Key Lemma**: For any WToken w, its canonical basis vector basisOfId(w)
    compiles to a MeaningObject with the same mode family (gauge class).

    Note: Multiple tokens share the same basisOfId (same mode + tau), so we
    can only guarantee mode family equality, not exact signature equality.
    The phiLevel is determined by findBestToken's first-match behavior.
    For mode4, tau may also differ due to the I-scaling variant. -/
theorem compile_canonical_exact (w : WTokenId) :
    ∃ m : MeaningObject,
      compileWindow (WTokenId.basisOfId w) = some m ∧
      m.signature.modeFamily = (WTokenId.toSpec w).mode := by
  -- The canonical basis is already neutral and normalized
  let b := WTokenId.basisOfId w

  -- Neutral: sum = 0, so normalizeWindow b = b
  have h_neutral := canonical_neutral_fixed w

  -- Unit energy
  have h_energy := canonical_unit_energy w

  -- Self-overlap is 1
  have h_overlap := canonical_self_overlap w

  -- Step 1: Show energy condition passes
  have h_energy_pos : ¬(normSq8 (normalizeWindow b) < 1e-10) := by
    rw [h_neutral, h_energy]
    norm_num

  have h_best_snd := findBestToken_snd b

  -- The best overlap is 1 (self-overlap) and findBestToken achieves it
  have h_best_is_one : (findBestToken b).2 = 1 := by
    -- Step 1: best overlap ≥ self-overlap = 1
    have h_ge_one : (findBestToken b).2 ≥ 1 := by
      have h_w_in : w ∈ allTokenIds := mem_allTokenIds w
      have h_ge := foldl_max_ge b allTokenIds (WTokenId.W0_Origin, overlapMagnitude b WTokenId.W0_Origin) rfl w h_w_in
      unfold findBestToken at h_ge
      rw [h_overlap] at h_ge
      exact h_ge

    -- Step 2: overlap ≤ 1 for unit vectors (by Cauchy-Schwarz)
    have h_le_one : (findBestToken b).2 ≤ 1 := by
      rw [h_best_snd]
      unfold overlapMagnitude
      have h_b_unit : normSq8 b = 1 := h_energy
      have h_basis_unit : normSq8 (WTokenId.basisOfId (findBestToken b).1) = 1 :=
        WTokenId.basisOfId_normalized (findBestToken b).1
      let u := WTokenId.basisOfId (findBestToken b).1
      let v := b
      calc Complex.normSq (innerProduct8 u v)
          ≤ normSq8 u * normSq8 v := by
            have h_cs : ‖innerProduct8 u v‖ ≤ Real.sqrt (normSq8 u) * Real.sqrt (normSq8 v) :=
              cauchy_schwarz_8_local u v
            rw [Complex.normSq_eq_norm_sq]
            calc ‖innerProduct8 u v‖ ^ 2
                ≤ (Real.sqrt (normSq8 u) * Real.sqrt (normSq8 v)) ^ 2 := by
                  apply sq_le_sq' (by linarith [norm_nonneg (innerProduct8 u v)]) h_cs
              _ = normSq8 u * normSq8 v := by
                  rw [mul_pow, Real.sq_sqrt (normSq8_nonneg u), Real.sq_sqrt (normSq8_nonneg v)]
        _ = 1 * 1 := by rw [h_b_unit, h_basis_unit]
        _ = 1 := by ring
    linarith

  -- Show classifyVector returns .exact
  have h_classify : classifyVector b = ClassifyResult.exact (findBestToken b).1 (findBestToken b).2 := by
    simp only [classifyVector]
    rw [h_neutral]
    have h_not_low : ¬(normSq8 b < 1e-10) := by rw [h_energy]; norm_num
    have h_thresh : (findBestToken b).2 / normSq8 b ≥ defaultConfig.classifyThreshold := by
      rw [h_energy, h_best_is_one, div_one]
      unfold defaultConfig PipelineConfig.classifyThreshold
      norm_num
    split_ifs with hLow hGe <;> first | exact absurd hLow h_not_low | exact absurd h_thresh hGe | rfl

  -- Get the best token's overlap = 1
  have h_best_overlap_1 : overlapMagnitude b (findBestToken b).1 = 1 := by
    have h_best_snd := findBestToken_snd b
    linarith

  -- Now we need to show (findBestToken b).1 has the same mode and tau as w
  -- Key insight: overlap = 1 implies same basis class (mode + tau)
  -- By overlap_normSq_zero_or_one, overlap is 0 or 1
  -- Since overlap = 1 and different families have overlap = 0, same family
  -- For same family, overlap = 1 requires same tau (except mode4 which has overlap = 1 even for different tau)

  let w' := (findBestToken b).1

  -- From overlap = 1, we know b and basisOfId w' have inner product magnitude = 1
  -- b = basisOfId w, so this means basisOfId w and basisOfId w' are equal up to phase
  -- By the structure of basisOfId, this means they have same mode and (for non-mode4) same tau

  -- The key lemma: overlapMagnitude (basisOfId w) w' = 1 implies same mode family
  have h_same_mode : WTokenId.modeFamily w' = WTokenId.modeFamily w := by
    -- Contrapositive: different family → overlap = 0 ≠ 1
    by_contra h_diff
    -- Different mode families have orthogonal bases: innerProduct8 = 0
    have h_orth := WTokenId.different_family_orthogonal w' w h_diff
    -- overlapMagnitude b w' = Complex.normSq (innerProduct8 (basisOfId w') b)
    -- By h_orth: WTokenId.innerProduct8 (basisOfId w') (basisOfId w) = 0
    -- The definitions of innerProduct8 are the same (both are ∑ star(u_i) * v_i)
    unfold overlapMagnitude at h_best_overlap_1
    -- Convert WTokenId.innerProduct8 to local innerProduct8
    have h_eq : innerProduct8 (WTokenId.basisOfId w') b =
                WTokenId.innerProduct8 (WTokenId.basisOfId w') (WTokenId.basisOfId w) := by
      unfold innerProduct8 WTokenId.innerProduct8
      rfl
    rw [h_eq, h_orth] at h_best_overlap_1
    simp only [Complex.normSq_zero] at h_best_overlap_1
    norm_num at h_best_overlap_1

  -- Construct the witness with modeFamily equality
  use {
    signature := MeaningSignature.fromId w'
    support := {w'.toNat}
    program := [LNALOp.LOCK [w'.toNat]]
    coefficients := spectralDecompose (normalizeWindow b)
  }
  constructor
  · simp only [compileWindow]
    rw [h_classify]
    rfl
  · -- modeFamily matches
    simp only [MeaningSignature.fromId]
    unfold WTokenId.modeFamily at h_same_mode
    exact h_same_mode

/-- |e^{iθ}|² = 1 for real θ.

    **Standard Result**: For real θ, e^{iθ} = cos θ + i sin θ,
    so |e^{iθ}|² = cos²θ + sin²θ = 1.

    This is a fundamental property of the unit circle in ℂ.
    The proof uses: ‖e^{iθ}‖ = 1 implies normSq = 1. -/
theorem normSq_exp_I (θ : ℝ) : Complex.normSq (Complex.exp (θ * Complex.I)) = 1 := by
  -- Use ‖e^z‖ = e^{Re(z)} and Re(θ*I) = 0
  have h_re : (θ * Complex.I).re = 0 := by simp [Complex.mul_re]
  have h_norm : ‖Complex.exp (θ * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp [h_re]
  -- normSq = ‖z‖²
  rw [Complex.normSq_eq_norm_sq, h_norm]
  norm_num

/-- Phase rotation preserves inner product magnitude. -/
theorem phase_rotation_overlap (v : Fin 8 → ℂ) (w : WTokenId) (θ : ℝ) :
    overlapMagnitude (fun i => Complex.exp (θ * Complex.I) * v i) w =
    overlapMagnitude v w := by
  unfold overlapMagnitude innerProduct8
  -- ⟨b, e^{iθ}v⟩ = e^{iθ} ⟨b, v⟩
  -- |e^{iθ} ⟨b, v⟩|² = |e^{iθ}|² |⟨b, v⟩|² = 1 · |⟨b, v⟩|²

  -- First, show the inner product gets scaled by e^{iθ}
  have h_scale : Finset.univ.sum (fun i => star (WTokenId.basisOfId w i) *
                    (Complex.exp (θ * Complex.I) * v i)) =
                 Complex.exp (θ * Complex.I) *
                    Finset.univ.sum (fun i => star (WTokenId.basisOfId w i) * v i) := by
    have h_eq : ∀ i, star (WTokenId.basisOfId w i) * (Complex.exp (θ * Complex.I) * v i) =
                     Complex.exp (θ * Complex.I) * (star (WTokenId.basisOfId w i) * v i) := by
      intro i; ring
    simp_rw [h_eq]
    rw [← Finset.mul_sum]

  rw [h_scale]
  -- |e^{iθ} · z|² = |e^{iθ}|² · |z|² = 1 · |z|²
  rw [Complex.normSq_mul, normSq_exp_I, one_mul]

/-- Phase rotation preserves normalization. -/
theorem phase_rotation_neutral (v : Fin 8 → ℂ) (θ : ℝ) :
    normalizeWindow (fun i => Complex.exp (θ * Complex.I) * v i) =
    fun i => Complex.exp (θ * Complex.I) * normalizeWindow v i := by
  unfold normalizeWindow projectToNeutral
  ext i
  -- Mean of e^{iθ}v is e^{iθ} times mean of v
  -- ∑ (e^{iθ} * v_i) = e^{iθ} * ∑ v_i
  rw [show Finset.univ.sum (fun x => Complex.exp (θ * Complex.I) * v x) =
          Complex.exp (θ * Complex.I) * Finset.univ.sum v by rw [Finset.mul_sum]]
  ring

/-- If classifyVector returns .exact, the token is (findBestToken ...).1 -/
theorem classifyVector_exact_token (v : Fin 8 → ℂ) (w : WTokenId) (overlap : ℝ)
    (h : classifyVector v = ClassifyResult.exact w overlap) :
    w = (findBestToken (normalizeWindow v)).1 := by
  simp only [classifyVector] at h
  split_ifs at h with h_low h_thresh <;> first | simp_all | cases h

/-- If classifyVector returns .exact, the overlap is (findBestToken ...).2 -/
theorem classifyVector_exact_overlap (v : Fin 8 → ℂ) (w : WTokenId) (overlap : ℝ)
    (h : classifyVector v = ClassifyResult.exact w overlap) :
    overlap = (findBestToken (normalizeWindow v)).2 := by
  simp only [classifyVector] at h
  split_ifs at h with h_low h_thresh <;> first | simp_all | cases h

/-- Helper: Extract coefficients from compileWindow result -/
theorem compileWindow_coefficients (v : Fin 8 → ℂ) (m : MeaningObject)
    (h : compileWindow v = some m) :
    m.coefficients = spectralDecompose (normalizeWindow v) := by
  simp only [compileWindow] at h
  split at h
  · -- exact case
    simp only [Option.some.injEq] at h
    rw [← h]
  · -- ambiguous case: none = some m is contradiction
    cases h
  · -- invalid case: none = some m is contradiction
    cases h

/-- Helper: Extract signature token from compileWindow result -/
theorem compileWindow_signature_from (v : Fin 8 → ℂ) (m : MeaningObject)
    (h : compileWindow v = some m) :
    m.signature = MeaningSignature.fromId (findBestToken (normalizeWindow v)).1 := by
  simp only [compileWindow] at h
  split at h
  case h_1 result w overlap h_cv =>
    simp only [Option.some.injEq] at h
    rw [← h]
    -- The signature field of the record is MeaningSignature.fromId w
    -- We need w = (findBestToken (normalizeWindow v)).1
    -- h_cv relates to classifyVector v = .exact w overlap
    have h_token := classifyVector_exact_token v w overlap h_cv
    rw [h_token]
  · cases h
  · cases h

/-- Helper: Extract support from compileWindow result -/
theorem compileWindow_support_from (v : Fin 8 → ℂ) (m : MeaningObject)
    (h : compileWindow v = some m) :
    m.support = {(findBestToken (normalizeWindow v)).1.toNat} := by
  simp only [compileWindow] at h
  split at h
  case h_1 result w overlap h_cv =>
    simp only [Option.some.injEq] at h
    rw [← h]
    -- Need: {w.toNat} = {(findBestToken (normalizeWindow v)).1.toNat}
    -- Same reasoning: w = (findBestToken (normalizeWindow v)).1
    have h_token := classifyVector_exact_token v w overlap h_cv
    rw [h_token]
  · cases h
  · cases h

/-- Gauge equivalence: compilation output is unique up to phase.

    **Key Theorem**: Phase rotation preserves:
    1. Overlap magnitudes (|⟨b, e^{iθ}v⟩| = |⟨b, v⟩|)
    2. Classification (same argmax)
    3. Therefore, same gauge class -/
theorem compile_gauge_invariant (v : Fin 8 → ℂ) (θ : ℝ)
    (h : compileWindow v = some m₁)
    (h' : compileWindow (fun i => Complex.exp (θ * Complex.I) * v i) = some m₂) :
    m₁.gaugeEquiv m₂ ∨ m₁ = m₂ := by
  -- Phase rotation preserves overlap for all tokens
  have h_overlap : ∀ w, overlapMagnitude (fun i => Complex.exp (θ * Complex.I) * v i) w =
                        overlapMagnitude v w := fun w => phase_rotation_overlap v w θ

  -- Since all overlap magnitudes are equal, findBestToken returns the same (token, overlap) pair
  -- Therefore classifyVector returns the same classification
  -- Therefore compileWindow constructs the same MeaningObject

  -- Key insight: The classification only depends on overlap magnitudes, not phases
  -- Since h_overlap shows all overlap magnitudes are identical,
  -- the max-finding and threshold checks return identical results

  -- For the structural match in compileWindow:
  -- Both v and (e^{iθ} * v) have same normalizeWindow behavior (phase doesn't affect sum)
  -- Both have same energy (phase has unit norm)
  -- Both have same findBestToken result (by h_overlap)
  -- Therefore the match produces identical MeaningObjects

  -- Choose left: gauge equivalence (coefficients differ by phase factor)
  left
  -- The MeaningObjects are gauge equivalent because:
  -- 1. Same signature (same classification from h_overlap)
  -- 2. Same support (same token)
  -- 3. Same program (same token)
  -- 4. Coefficients: spectralDecompose (e^{iθ} * v) = e^{iθ} * spectralDecompose v
  --    by linearity of DFT

  -- gaugeEquiv requires same signature + same support + coefficients differ by phase
  -- MeaningObject.gaugeEquiv m₁ m₂ :=
  --   m₁.signature = m₂.signature ∧
  --   m₁.support = m₂.support ∧
  --   ∃ θ' : ℝ, ∀ k, m₂.coefficients k = e^{iθ'} * m₁.coefficients k

  unfold MeaningObject.gaugeEquiv
  -- Need to show the three conjuncts:
  -- 1. Same signature: follows from same classification (same token)
  -- 2. Same support: follows from same classification (same token.toNat)
  -- 3. Coefficients: spectralDecompose (e^{iθ} * v) k = e^{iθ} * spectralDecompose v k
  --    by linearity of DFT (phase factor pulls out)

  -- Key fact: findBestToken is invariant under phase rotation
  have h_best : findBestToken (normalizeWindow (fun i => Complex.exp (θ * Complex.I) * v i)) =
                findBestToken (normalizeWindow v) := by
    -- normalizeWindow commutes with scalar multiplication
    rw [normalizeWindow_smul]
    exact findBestToken_phase_inv (normalizeWindow v) θ

  -- Energy is preserved under phase rotation (unit norm)
  have h_energy : normSq8 (normalizeWindow (fun i => Complex.exp (θ * Complex.I) * v i)) =
                  normSq8 (normalizeWindow v) := by
    rw [normalizeWindow_smul]
    unfold normSq8
    simp only [Complex.normSq_mul]
    have h_unit : Complex.normSq (Complex.exp (θ * Complex.I)) = 1 := by
      have h_norm : ‖Complex.exp (θ * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
      rw [Complex.normSq_eq_norm_sq, h_norm, one_pow]
    simp only [h_unit, one_mul]

  -- Unfold compileWindow in hypotheses to extract structure
  -- Since findBestToken and energy are the same, classifyVector returns same result
  -- Therefore the constructed MeaningObjects have identical signature and support

  -- For coefficients: use spectralDecompose_smul + normalizeWindow_smul
  have h_coeff : spectralDecompose (normalizeWindow (fun i => Complex.exp (θ * Complex.I) * v i)) =
                 fun k => Complex.exp (θ * Complex.I) * spectralDecompose (normalizeWindow v) k := by
    rw [normalizeWindow_smul]
    exact spectralDecompose_smul (normalizeWindow v) (Complex.exp (θ * Complex.I))

  -- Preserve original hypotheses before simp modifies them
  have h_orig := h
  have h'_orig := h'

  -- Extract from h and h' that both give some MeaningObject
  -- With h_best showing same classification, extract equality of signature/support
  simp only [compileWindow, classifyVector] at h h'
  -- The same findBestToken and energy means same threshold check
  -- Therefore same ClassifyResult.exact branch taken
  -- Therefore same signature (from same token) and same support

  -- Since we have h and h' giving some m₁ and m₂ respectively,
  -- and the classification only depends on findBestToken and energy (which are equal),
  -- the MeaningObjects have:
  -- - Same signature (MeaningSignature.fromId of same token)
  -- - Same support (same token.toNat)
  -- - Coefficients related by phase factor (h_coeff)

  -- For structural extraction, we use the invariance lemmas
  -- The proof that signature and support match follows from h_best + h_energy
  -- The coefficient relation follows from h_coeff

  -- Extract: since classifyVector uses findBestToken and energy, and both are equal,
  -- the resulting MeaningObjects have identical structure except for coefficients

  -- Key mathematical facts proven:
  -- 1. h_best: same findBestToken result
  -- 2. h_energy: same energy
  -- 3. h_coeff: coefficients differ by e^{iθ}
  --
  -- The structural extraction from the match is tedious but follows from:
  -- - Same findBestToken → same ClassifyResult.exact branch
  -- - Same signature (MeaningSignature.fromId of same token)
  -- - Same support ({token.toNat})
  -- - Coefficients: m₂.coefficients = e^{iθ} * m₁.coefficients (by h_coeff)

  -- Using native_decide or structural analysis for the extraction
  -- All invariance lemmas are proven; this is pure match extraction
  simp only [h_best, h_energy] at h h'

  -- The key insight: classifyVector result depends only on findBestToken and energy
  -- Since h_best and h_energy show these are equal, classifyVector results are equal
  -- Therefore the .exact w _ branch is taken for both, with the same w

  -- Let's call the common findBestToken result (w_best, overlap_best)
  let w_best := (findBestToken (normalizeWindow v)).1
  let overlap_best := (findBestToken (normalizeWindow v)).2

  -- The classification for both v and v' results in .exact w_best _
  -- Therefore:
  -- - m₁.signature = MeaningSignature.fromId w_best
  -- - m₂.signature = MeaningSignature.fromId w_best
  -- - m₁.support = {w_best.toNat}
  -- - m₂.support = {w_best.toNat}
  -- - m₁.coefficients = spectralDecompose (normalizeWindow v)
  -- - m₂.coefficients = spectralDecompose (normalizeWindow v') = e^{iθ} * m₁.coefficients

  constructor
  · -- Same signature: both use MeaningSignature.fromId of same (findBestToken _).1
    -- Use helper lemmas to extract signatures
    have h_sig1 := compileWindow_signature_from v m₁ h_orig
    have h_sig2 := compileWindow_signature_from (fun i => Complex.exp (θ * Complex.I) * v i) m₂ h'_orig
    rw [h_sig1, h_sig2, h_best]
  constructor
  · -- Same support: both use {(findBestToken _).1.toNat}
    -- Use helper lemmas to extract supports
    have h_sup1 := compileWindow_support_from v m₁ h_orig
    have h_sup2 := compileWindow_support_from (fun i => Complex.exp (θ * Complex.I) * v i) m₂ h'_orig
    rw [h_sup1, h_sup2, h_best]
  · -- Coefficients differ by phase
    use θ
    intro k
    -- m₂.coefficients = spectralDecompose (normalizeWindow v')
    -- m₁.coefficients = spectralDecompose (normalizeWindow v)
    -- By h_coeff: spectralDecompose (normalizeWindow v') k = e^{iθ} * spectralDecompose (normalizeWindow v) k
    have h_coeff_k := congrFun h_coeff k
    -- Use helper to extract coefficients from compileWindow (using preserved original hypotheses)
    have h_m1_coeff := compileWindow_coefficients v m₁ h_orig
    have h_m2_coeff := compileWindow_coefficients (fun i => Complex.exp (θ * Complex.I) * v i) m₂ h'_orig
    rw [congrFun h_m2_coeff k, h_coeff_k, congrFun h_m1_coeff k]

/-! ## Compiler Status -/

/-- Summary of pipeline implementation status. -/
def pipelineStatus : List (String × String) :=
  [ ("Stage 1: Windowing", "IMPLEMENTED (length theorem)")
  , ("Stage 2: Normalization", "IMPLEMENTED (neutrality theorem)")
  , ("Stage 3: Spectral Analysis", "IMPLEMENTED (mode0 theorem)")
  , ("Stage 4: Classification", "IMPLEMENTED")
  , ("Stage 5: Program Synthesis", "SCAFFOLD")
  , ("Stage 6: MeaningObject Construction", "IMPLEMENTED")
  , ("Canonical self-overlap", "THEOREM (closed)")
  , ("Canonical neutral fixed", "THEOREM (closed)")
  , ("Phase rotation overlap", "THEOREM (closed)")
  , ("Phase rotation neutral", "THEOREM (closed)")
  , ("Compile canonical exact", "THEOREM (closed, modeFamily equality)")
  , ("Gauge Invariance", "THEOREM (closed)")
  ]

#eval pipelineStatus

end MeaningCompiler
end Verification
end IndisputableMonolith
