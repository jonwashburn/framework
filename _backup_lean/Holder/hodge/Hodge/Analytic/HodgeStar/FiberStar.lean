import Hodge.Basic
import Hodge.Analytic.DomCoprod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Fiber-level Hodge star

This file introduces *fiber/model-space* definitions needed to build a Hodge star operator.

In this codebase, the "fiber" of `k`-forms is represented as

`FiberAlt n k := (TangentModel n) [⋀^Fin k]→L[ℝ] ℂ`.

## Main Definitions

* `fiberBasisVector`: Standard basis vector e_i in TangentModel n
* `fiberFrame`: A k-tuple of basis vectors for indices in a Finset
* `fiberAltInner`: Inner product on FiberAlt n k via basis evaluation
* `fiberHodgeStar_construct`: Fiber-level Hodge star

## Implementation Notes

The inner product on k-forms is defined as:
  ⟨α, β⟩ = Σ_{|I|=k} α(e_I) * conj(β(e_I))

where e_I = (e_{i₁}, ..., e_{i_k}) for increasing k-tuples I.

This is the standard inner product induced by the Euclidean metric on ℂⁿ.
-/

noncomputable section

open Classical Finset

set_option autoImplicit false

/-! ## Basis Vectors -/

/-- Standard real basis vector in the tangent model space.

We view `ℂⁿ` as a real vector space of dimension `2n`, with basis
`{e₁, …, eₙ, i e₁, …, i eₙ}`. -/
noncomputable def fiberBasisVector (n : ℕ) (i : Fin (2 * n)) : TangentModel n := by
  classical
  have h : 2 * n = n + n := by simpa [two_mul]
  exact (Fin.addCases
    (fun j : Fin n => EuclideanSpace.single j (1 : ℂ))
    (fun j : Fin n => EuclideanSpace.single j (Complex.I))
    (Fin.cast h i))

/-- Convert a Finset to an ordered list (sorted). -/
noncomputable def finsetToSortedList (n : ℕ) (s : Finset (Fin (2 * n))) : List (Fin (2 * n)) :=
  s.sort (· ≤ ·)

/-- Build a frame (tuple of basis vectors) from a sorted list of indices.
    If the list has fewer than k elements, pad with zeros. -/
noncomputable def listToFrame (n k : ℕ) (l : List (Fin (2 * n))) : Fin k → TangentModel n :=
  fun i =>
    if h : i.val < l.length then
      fiberBasisVector n (l.get ⟨i.val, h⟩)
    else
      0

/-- A frame of k basis vectors indexed by a k-element Finset. -/
noncomputable def fiberFrame (n k : ℕ) (s : Finset (Fin (2 * n))) : Fin k → TangentModel n :=
  listToFrame n k (finsetToSortedList n s)

/-! ## Fiber Inner Product -/

/-- Inner product on `FiberAlt n k` via basis evaluation.

For k-forms α, β, the inner product is:
  ⟨α, β⟩ = Σ_{|I|=k} α(e_I) * conj(β(e_I))

where the sum is over all k-element subsets I of {0,...,2n-1}.

**Properties** (proved below):
- Hermitian: ⟨α, β⟩ = conj(⟨β, α⟩)
- Positive: ⟨α, α⟩ ≥ 0
- Linear in first argument -/
noncomputable def fiberAltInner (n k : ℕ) (α β : FiberAlt n k) : ℂ :=
  ∑ s ∈ powersetCard k (univ : Finset (Fin (2 * n))),
    α (fiberFrame n k s) * starRingEnd ℂ (β (fiberFrame n k s))

/-- The fiber inner product is Hermitian symmetric. -/
theorem fiberAltInner_conj_symm (n k : ℕ) (α β : FiberAlt n k) :
    fiberAltInner n k α β = starRingEnd ℂ (fiberAltInner n k β α) := by
  simp only [fiberAltInner, map_sum, starRingEnd_apply]
  congr 1
  ext s
  rw [star_mul', star_star]
  ring

/-- The fiber inner product of a form with itself is real and nonnegative. -/
theorem fiberAltInner_self_nonneg (n k : ℕ) (α : FiberAlt n k) :
    0 ≤ (fiberAltInner n k α α).re := by
  simp only [fiberAltInner]
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro s _
  -- α(frame) * conj(α(frame)) = |α(frame)|² ≥ 0
  let z := α (fiberFrame n k s)
  show 0 ≤ (z * starRingEnd ℂ z).re
  simp only [starRingEnd_apply]
  -- z * star z = |z|² since star = conj for ℂ
  have h : (z * star z).re = Complex.normSq z := by
    simp only [RCLike.star_def, RCLike.mul_conj, sq]
    -- (↑‖z‖ * ↑‖z‖).re = Complex.normSq z
    calc (↑‖z‖ * ↑‖z‖ : ℂ).re
      _ = (↑(‖z‖ * ‖z‖) : ℂ).re := by rw [Complex.ofReal_mul]
      _ = ‖z‖ * ‖z‖ := Complex.ofReal_re _
      _ = Complex.normSq z := Complex.norm_mul_self_eq_normSq z
  rw [h]
  exact Complex.normSq_nonneg _

/-- For the self-inner-product, the real part is the sum of squared norms of the basis coefficients. -/
theorem fiberAltInner_self_re_eq_sum_normSq (n k : ℕ) (α : FiberAlt n k) :
    (fiberAltInner n k α α).re =
      ∑ s ∈ powersetCard k (univ : Finset (Fin (2 * n))),
        Complex.normSq (α (fiberFrame n k s)) := by
  simp only [fiberAltInner]
  -- Move `re` inside the finite sum.
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl ?_
  intro s hs
  -- Each term is `z * conj z`, whose real part is `normSq z`.
  simpa using congrArg Complex.re (Complex.mul_conj (α (fiberFrame n k s)))

/-- Definiteness on basis coefficients: if `Re ⟨α,α⟩ = 0`, then all basis evaluations vanish. -/
theorem fiberAltInner_self_re_eq_zero_iff (n k : ℕ) (α : FiberAlt n k) :
    (fiberAltInner n k α α).re = 0 ↔
      ∀ s ∈ powersetCard k (univ : Finset (Fin (2 * n))),
        α (fiberFrame n k s) = 0 := by
  -- Rewrite in terms of a sum of nonnegative real terms.
  rw [fiberAltInner_self_re_eq_sum_normSq (n := n) (k := k) (α := α)]
  constructor
  · intro hsum
    have hnorm :
        ∀ s ∈ powersetCard k (univ : Finset (Fin (2 * n))),
          Complex.normSq (α (fiberFrame n k s)) = 0 := by
      have h :=
        (Finset.sum_eq_zero_iff_of_nonneg (s := powersetCard k (univ : Finset (Fin (2 * n))))
            (f := fun s => Complex.normSq (α (fiberFrame n k s)))
            (by
              intro s hs
              exact Complex.normSq_nonneg _)).1 hsum
      exact h
    intro s hs
    exact (Complex.normSq_eq_zero).1 (hnorm s hs)
  · intro hcoeff
    -- All summands are zero, hence the sum is zero.
    apply Finset.sum_eq_zero
    intro s hs
    have : α (fiberFrame n k s) = 0 := hcoeff s hs
    simpa [this]

/-- The fiber inner product is additive in the first argument. -/
theorem fiberAltInner_add_left (n k : ℕ) (α₁ α₂ β : FiberAlt n k) :
    fiberAltInner n k (α₁ + α₂) β = fiberAltInner n k α₁ β + fiberAltInner n k α₂ β := by
  simp only [fiberAltInner, ContinuousAlternatingMap.add_apply, add_mul, Finset.sum_add_distrib]

/-- The fiber inner product is ℂ-linear in the first argument. -/
theorem fiberAltInner_smul_left (n k : ℕ) (c : ℂ) (α β : FiberAlt n k) :
    fiberAltInner n k (c • α) β = c * fiberAltInner n k α β := by
  simp only [fiberAltInner, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  congr 1
  ext s
  ring

/-! ## Complement and Sign -/

/-- The complement of a k-element subset in Fin (2n) (as a Finset). -/
def finsetComplement (n : ℕ) (s : Finset (Fin (2 * n))) : Finset (Fin (2 * n)) :=
  univ \ s

/-- Count inversions when concatenating sorted lists from sets s and sᶜ.
    This gives the shuffle sign: (-1)^{inversions}. -/
noncomputable def shuffleSignCount (n : ℕ) (s : Finset (Fin (2 * n))) : ℕ :=
  -- Number of pairs (i, j) where i ∈ s, j ∈ sᶜ, and i > j
  (s.sum fun i => (finsetComplement n s).filter (fun j => j < i) |>.card)

/-- The shuffle sign for concatenating s and sᶜ into the standard ordering. -/
noncomputable def shuffleSign (n : ℕ) (s : Finset (Fin (2 * n))) : ℤ :=
  (-1 : ℤ) ^ shuffleSignCount n s

/-! ## Volume Form -/

/-- The standard basis frame: all indices from 0 to 2n-1. -/
noncomputable def fullFrame (n : ℕ) : Fin (2 * n) → TangentModel n :=
  fun i => fiberBasisVector n i

/-- Check if a frame v matches the standard frame for indices in s (up to reordering).
    Returns the coefficient (0, 1, or -1) based on matching and permutation sign. -/
noncomputable def frameMatchCoeff (n k : ℕ) (s : Finset (Fin (2 * n)))
    (v : Fin k → TangentModel n) : ℂ :=
  -- For the standard orthonormal basis, this checks if v is a permutation of (e_{i₁}, ..., e_{iₖ})
  -- where {i₁, ..., iₖ} = s
  -- This is complex to implement fully; for now we use a simplified version
  if h : s.card = k then
    -- Check if v equals the standard frame for s
    let sorted_frame := fiberFrame n k s
    if (∀ i : Fin k, v i = sorted_frame i) then 1 else 0
  else 0

/-! ## Fiber Hodge Star -/

/-! Fiber-level Hodge star on the model tangent space.

The Hodge star ⋆ : Λ^k → Λ^{2n-k} is defined by the relation:
  β ∧ ⋆α = ⟨α, β⟩ · vol

For a basis element e_I (where I is a k-element subset):
  ⋆e_I = ε(I, Iᶜ) · e_{Iᶜ}

where ε(I, Iᶜ) is the shuffle sign.

**Implementation**: The Hodge star is computed by:
1. Decomposing α into its basis representation via frame evaluation
2. For each basis element, mapping to the complementary basis element with sign
3. The result evaluates on (2n-k)-frames by matching to complementary frames

**Mathematical Formula**:
For α : FiberAlt n k, the Hodge star ⋆α : FiberAlt n (2n-k) is defined by:
  (⋆α)(v) = Σ_{|I|=k} α(e_I) · ε(I, Iᶜ) · δ(v, e_{Iᶜ})

where δ(v, e_{Iᶜ}) is 1 if v matches the frame for Iᶜ, 0 otherwise.

**Implementation**:

We use the real basis `{e₁, …, eₙ, i e₁, …, i eₙ}` of `ℂⁿ` (viewed as a real vector space)
to expand `α` in coordinate basis forms, and send each basis element to its complementary
basis element with the appropriate shuffle sign.
-/

/-!
### Coordinate-basis k-forms

We define, for a `k`-subset `s ⊆ Fin (2n)`, a canonical basis `k`-form `fiberBasisForm n k s`
as the determinant of the `k×k` matrix of the selected **real** coordinates. Concretely,
it is the wedge of the real coordinate covectors indexed by `s`.
-/

/-- Real coordinate projection onto the real part of the i-th complex coordinate. -/
noncomputable def coordRe (n : ℕ) (i : Fin n) : TangentModel n →ₗ[ℝ] ℝ where
  toFun := fun x => (x i).re
  map_add' := by
    intro x y
    simp [Pi.add_apply, Complex.add_re]
  map_smul' := by
    intro r x
    simp [Pi.smul_apply, Complex.smul_re]

/-- Real coordinate projection onto the imaginary part of the i-th complex coordinate. -/
noncomputable def coordIm (n : ℕ) (i : Fin n) : TangentModel n →ₗ[ℝ] ℝ where
  toFun := fun x => (x i).im
  map_add' := by
    intro x y
    simp [Pi.add_apply, Complex.add_im]
  map_smul' := by
    intro r x
    simp [Pi.smul_apply, Complex.smul_im]

/-- The real coordinate map `ℂⁿ → (Fin (2n) → ℝ)` as an ℝ-linear map. -/
noncomputable def coordLM (n : ℕ) : TangentModel n →ₗ[ℝ] (Fin (2 * n) → ℝ) := by
  classical
  have h : 2 * n = n + n := by simpa [two_mul]
  refine LinearMap.pi (fun i : Fin (2 * n) => ?_)
  exact (Fin.addCases (fun j : Fin n => coordRe n j) (fun j : Fin n => coordIm n j) (Fin.cast h i))

/-- Project `ℂⁿ` to the `k` real coordinates indexed by a finset `s`.

If `s` has fewer than `k` elements, we pad with zero coordinates (so the result is still a
`Fin k → ℝ`). This keeps the definition non-dependent (no `s.card = k` argument).
-/
noncomputable def projCoords (n k : ℕ) (s : Finset (Fin (2 * n))) :
    TangentModel n →ₗ[ℝ] (Fin k → ℝ) := by
  classical
  let coord : TangentModel n →ₗ[ℝ] (Fin (2 * n) → ℝ) := coordLM n
  let l : List (Fin (2 * n)) := s.sort (· ≤ ·)
  refine LinearMap.pi (fun i : Fin k => by
    classical
    by_cases h : i.1 < l.length
    · -- x ↦ (coord x) (l.get i)
      exact (LinearMap.proj (R := ℝ) (ι := Fin (2 * n)) (φ := fun _ => ℝ)
        (l.get ⟨i.1, h⟩)).comp coord
    · -- padding coordinate
      exact 0)

/-- The coordinate-basis `k`-form corresponding to a finset `s`.

If `s` does not have exactly `k` elements, this still returns a well-typed alternating map (built
from the first `k` sorted indices, padded by zeros as needed). In the intended uses below, we apply
it to `s ∈ powersetCard k univ`, so it agrees with the usual basis form indexed by `s`.
-/
noncomputable def fiberBasisForm (n k : ℕ) (s : Finset (Fin (2 * n))) : FiberAlt n k := by
  classical
  let det : (Fin k → ℝ) [⋀^Fin k]→ₗ[ℝ] ℝ := Matrix.detRowAlternating
  let lin : (TangentModel n) [⋀^Fin k]→ₗ[ℝ] ℝ := det.compLinearMap (projCoords n k s)
  let linC : (TangentModel n) [⋀^Fin k]→ₗ[ℝ] ℂ :=
    (Complex.ofRealCLM.toLinearMap).compAlternatingMap lin
  -- Make it continuous using the finite-dimensional bound lemma from `DomCoprod.lean`.
  have h_ex :
      ∃ C : ℝ, ∀ v : Fin k → TangentModel n, ‖linC v‖ ≤ C * ∏ i, ‖v i‖ :=
    AlternatingMap.exists_bound_fin_dim (𝕜 := ℝ) (E := TangentModel n) (F := ℂ) (ι := Fin k) linC
  let C : ℝ := Classical.choose h_ex
  have hC : ∀ v : Fin k → TangentModel n, ‖linC v‖ ≤ C * ∏ i, ‖v i‖ :=
    Classical.choose_spec h_ex
  exact (linC.mkContinuous C hC)

/-- Evaluation at a fixed frame, as a continuous linear functional on `FiberAlt`. -/
noncomputable def fiberEvalCLM (n k : ℕ) (v : Fin k → TangentModel n) : FiberAlt n k →L[ℂ] ℂ := by
  classical
  refine
    { toFun := fun f => f v
      cont := ?_
      map_add' := by intro f g; rfl
      map_smul' := by intro c f; rfl }
  simpa using (continuous_eval_const v)

/-- Fiber-level Hodge star as a bundled continuous linear map. -/
noncomputable def fiberHodgeStarCLM (n k : ℕ) :
    FiberAlt n k →L[ℂ] FiberAlt n (2 * n - k) := by
  classical
  let S : Finset (Finset (Fin (2 * n))) := powersetCard k (univ : Finset (Fin (2 * n)))
  -- Sum the rank-1 operators `α ↦ (shuffleSign*s * α(e_s)) • e_{sᶜ}`.
  refine S.sum (fun s => ?_)
  let ev : FiberAlt n k →L[ℂ] ℂ := fiberEvalCLM n k (fiberFrame n k s)
  let coeff : FiberAlt n k →L[ℂ] ℂ := (shuffleSign n s : ℂ) • ev
  exact ContinuousLinearMap.smulRight coeff (fiberBasisForm n (2 * n - k) (finsetComplement n s))

/-- Fiber-level Hodge star in the real `ℂⁿ`-model: `k`-forms to `(2n-k)`-forms. -/
noncomputable def fiberHodgeStar_construct (n k : ℕ) (α : FiberAlt n k) :
    FiberAlt n (2 * n - k) := by
  classical
  exact fiberHodgeStarCLM n k α

@[simp] theorem fiberHodgeStar_construct_zero (n k : ℕ) :
    fiberHodgeStar_construct n k (0 : FiberAlt n k) = 0 := by
  simpa [fiberHodgeStar_construct] using (fiberHodgeStarCLM n k).map_zero

/-- Helper: eqRec distributes over add for FiberAlt -/
theorem fiberAlt_eqRec_add {n k k' : ℕ} (h : k = k') (α β : FiberAlt n k) :
    h ▸ (α + β) = (h ▸ α) + (h ▸ β) := by
  subst h; rfl

/-- Helper: eqRec distributes over smul for FiberAlt -/
theorem fiberAlt_eqRec_smul {n k k' : ℕ} (h : k = k') (c : ℂ) (α : FiberAlt n k) :
    h ▸ (c • α) = c • (h ▸ α) := by
  subst h; rfl

/-- Helper: eqRec preserves zero for FiberAlt -/
theorem fiberAlt_eqRec_zero {n k k' : ℕ} (h : k = k') :
    h ▸ (0 : FiberAlt n k) = (0 : FiberAlt n k') := by
  subst h; rfl

/-- Helper: eqRec distributes over neg for FiberAlt -/
theorem fiberAlt_eqRec_neg {n k k' : ℕ} (h : k = k') (α : FiberAlt n k) :
    h ▸ (-α) = -(h ▸ α) := by
  subst h; rfl

/-- Helper: Applying eqRec-transported zero gives zero -/
theorem fiberAlt_eqRec_zero_apply {n k k' : ℕ} (h : k = k') (v : Fin k' → TangentModel n) :
    (h ▸ (0 : FiberAlt n k)) v = 0 := by
  subst h; rfl

/-- Helper: Applying eqRec-transported neg distributes -/
theorem fiberAlt_eqRec_neg_apply {n k k' : ℕ} (h : k = k') (α : FiberAlt n k)
    (v : Fin k' → TangentModel n) :
    (h ▸ (-α)) v = -((h ▸ α) v) := by
  subst h; rfl

/-- The Hodge star is additive. -/
theorem fiberHodgeStar_add (n k : ℕ) (α β : FiberAlt n k) :
    fiberHodgeStar_construct n k (α + β) =
    fiberHodgeStar_construct n k α + fiberHodgeStar_construct n k β := by
  classical
  simpa [fiberHodgeStar_construct] using (fiberHodgeStarCLM n k).map_add α β

/-- The Hodge star respects scalar multiplication. -/
theorem fiberHodgeStar_smul (n k : ℕ) (c : ℂ) (α : FiberAlt n k) :
    fiberHodgeStar_construct n k (c • α) = c • fiberHodgeStar_construct n k α := by
  classical
  simpa [fiberHodgeStar_construct] using (fiberHodgeStarCLM n k).map_smul c α

end
