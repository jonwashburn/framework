import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel
import Hodge.Analytic.Currents
import Hodge.Analytic.FlatNorm

/-!
# Prefix template extension (TeX: `prop:sliver-template-extension`)

This file formalizes the purely combinatorial bookkeeping used in the TeX “sliver”/template
machinery:

If two objects are built from **prefixes of a common ordered template** (lengths `N₁`, `N₂`),
then the mismatch decomposes into a **matched** part (indices `< min N₁ N₂`) and an
**unmatched tail** (indices in the longer prefix but not the shorter).

No geometry is used here; this is just `Finset.range` algebra.
-/

noncomputable section

open Classical
open scoped BigOperators

namespace Hodge.TexSpine.Template

universe u

variable {n : ℕ} {X : Type u}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]
  [Nonempty X] [MeasurableSpace X] [BorelSpace X]

/-! ## Prefix sums -/

/-- The current obtained by summing the first `N` template pieces. -/
noncomputable def prefixSum {k : ℕ} (T : ℕ → Current n X k) (N : ℕ) : Current n X k :=
  ∑ i ∈ Finset.range N, T i

@[simp] lemma prefixSum_zero {k : ℕ} (T : ℕ → Current n X k) : prefixSum (n := n) (X := X) T 0 = 0 := by
  simp [prefixSum]

/-- `prefixSum` splits at `Nmin = min N₁ N₂`. -/
theorem prefixSum_split_min {k : ℕ} (T : ℕ → Current n X k) (N₁ N₂ : ℕ) :
    prefixSum (n := n) (X := X) T N₁ =
      prefixSum (n := n) (X := X) T (Nat.min N₁ N₂) +
        ∑ i ∈ (Finset.range N₁ \ Finset.range (Nat.min N₁ N₂)), T i := by
  classical
  -- Unfold the definition and split `range N₁` into the part below `min` and the tail.
  unfold prefixSum
  have hsubset : Finset.range (Nat.min N₁ N₂) ⊆ Finset.range N₁ := by
    intro i hi
    have : i < Nat.min N₁ N₂ := by
      simpa [Finset.mem_range] using hi
    have : i < N₁ := lt_of_lt_of_le this (Nat.min_le_left _ _)
    simpa [Finset.mem_range] using this
  have hdisj :
      Disjoint (Finset.range (Nat.min N₁ N₂))
        (Finset.range N₁ \ Finset.range (Nat.min N₁ N₂)) :=
    Finset.disjoint_sdiff
  have hrange :
      Finset.range N₁ =
        Finset.range (Nat.min N₁ N₂) ∪
          (Finset.range N₁ \ Finset.range (Nat.min N₁ N₂)) := by
    -- `A ⊆ B` ⇒ `A ∪ (B \ A) = B`
    simpa using (Finset.union_sdiff_of_subset hsubset).symm
  -- Rewrite only the LHS range as a disjoint union, then apply `sum_union`.
  calc
    (∑ i ∈ Finset.range N₁, T i)
        = ∑ i ∈ Finset.range (Nat.min N₁ N₂) ∪
              (Finset.range N₁ \ Finset.range (Nat.min N₁ N₂)), T i := by
            -- apply the range-splitting equality under the `Finset.sum` operator
            exact congrArg (fun s => ∑ i ∈ s, T i) hrange
    _ = (∑ i ∈ Finset.range (Nat.min N₁ N₂), T i) +
          ∑ i ∈ (Finset.range N₁ \ Finset.range (Nat.min N₁ N₂)), T i := by
            -- `sum_union` for disjoint finsets
            simpa using (Finset.sum_union hdisj (f := fun i => T i))

/-! ## Unmatched tail decomposition -/

/-- **Matched + unmatched tail decomposition** (TeX: `prop:sliver-template-extension`).

Let `S₁ = prefixSum T N₁` and `S₂ = prefixSum T N₂` be built from the same ordered template.
Then the mismatch decomposes as:

`S₁ - S₂ = (matched) + (unmatched)`

where the matched part uses indices `< min N₁ N₂` on both sides and the unmatched part
is supported on the tail indices of the longer prefix.
-/
theorem prefix_mismatch_decompose {k : ℕ} (T : ℕ → Current n X k) (N₁ N₂ : ℕ) :
    prefixSum (n := n) (X := X) T N₁ - prefixSum (n := n) (X := X) T N₂ =
      (∑ i ∈ (Finset.range N₁ \ Finset.range (Nat.min N₁ N₂)), T i) -
      (∑ i ∈ (Finset.range N₂ \ Finset.range (Nat.min N₁ N₂)), T i) := by
  classical
  -- Expand both prefix sums at `min`, then cancel the common prefix.
  have h1 := prefixSum_split_min (n := n) (X := X) (k := k) T N₁ N₂
  have h2raw := prefixSum_split_min (n := n) (X := X) (k := k) T N₂ N₁
  have h2 :
      prefixSum (n := n) (X := X) T N₂ =
        prefixSum (n := n) (X := X) T (Nat.min N₁ N₂) +
          ∑ i ∈ (Finset.range N₂ \ Finset.range (Nat.min N₁ N₂)), T i := by
    -- rewrite `min N₂ N₁` as `min N₁ N₂`
    simpa [Nat.min_comm] using h2raw
  -- Substitute and let `abel` cancel the shared prefix sum.
  rw [h1, h2]
  abel

end Hodge.TexSpine.Template

/-! ## Flat-norm bounds for template mismatches (formal)

This section upgrades the purely combinatorial `prefix_mismatch_decompose` into a purely formal
flat-norm estimate using the triangle inequality for `flatNorm`.

This is the Lean analogue of the TeX step:
“identify the unmatched tail, then bound the mismatch by the sum of per-piece errors”.
-/

namespace Hodge.TexSpine.TemplateFlat

universe u

variable {n : ℕ} {X : Type u}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]
  [Nonempty X] [MeasurableSpace X] [BorelSpace X]

open Hodge.TexSpine.Template

/-- Triangle inequality for `flatNorm` over a `Finset.sum`. -/
theorem flatNorm_sum_le_sum_flatNorm {ι : Type*} {k : ℕ} (s : Finset ι) (T : ι → Current n X k) :
    _root_.flatNorm (n := n) (X := X) (k := k) (∑ i ∈ s, T i) ≤
      ∑ i ∈ s, _root_.flatNorm (n := n) (X := X) (k := k) (T i) := by
  classical
  refine Finset.induction_on s ?h0 ?hstep
  · simp [_root_.flatNorm_zero (n := n) (X := X) (k := k)]
  · intro a s ha ih
    -- split off the head, apply `flatNorm_add_le`, then use IH
    simpa [ha, Finset.sum_insert, add_assoc, add_left_comm, add_comm] using
      (calc
        _root_.flatNorm (n := n) (X := X) (k := k) (T a + ∑ i ∈ s, T i)
            ≤ _root_.flatNorm (n := n) (X := X) (k := k) (T a) +
                _root_.flatNorm (n := n) (X := X) (k := k) (∑ i ∈ s, T i) := by
                  simpa using
                    (_root_.flatNorm_add_le (n := n) (X := X) (k := k) (T a) (∑ i ∈ s, T i))
        _ ≤ _root_.flatNorm (n := n) (X := X) (k := k) (T a) +
                ∑ i ∈ s, _root_.flatNorm (n := n) (X := X) (k := k) (T i) := by
              -- add the same constant on the left to the induction hypothesis
              -- `add_le_add_left` in this environment adds on the *right*, so commutate.
              simpa [add_comm, add_left_comm, add_assoc] using
                (add_le_add_left ih (_root_.flatNorm (n := n) (X := X) (k := k) (T a)))
        )

/-- **Unmatched-tail ⇒ flat-norm bound** for two prefix sums.

This is the formal spine behind TeX Prop `sliver-template-extension` + “transport ⇒ flat control”:
the mismatch is controlled by the sum of per-term flat norms on the unmatched tails.
-/
theorem flatNorm_prefix_mismatch_le_unmatched {k : ℕ} (T : ℕ → Current n X k) (N₁ N₂ : ℕ) :
    _root_.flatNorm (n := n) (X := X) (k := k) (prefixSum (n := n) (X := X) (k := k) T N₁ - prefixSum (n := n) (X := X) (k := k) T N₂)
      ≤
        (∑ i ∈ (Finset.range N₁ \ Finset.range (Nat.min N₁ N₂)),
            _root_.flatNorm (n := n) (X := X) (k := k) (T i)) +
        (∑ i ∈ (Finset.range N₂ \ Finset.range (Nat.min N₁ N₂)),
            _root_.flatNorm (n := n) (X := X) (k := k) (T i)) := by
  classical
  -- rewrite mismatch as difference of tails
  have hdecomp :=
    prefix_mismatch_decompose (n := n) (X := X) (k := k) T N₁ N₂
  -- abbreviate the two unmatched tails
  let A : Current n X k := ∑ i ∈ (Finset.range N₁ \ Finset.range (Nat.min N₁ N₂)), T i
  let B : Current n X k := ∑ i ∈ (Finset.range N₂ \ Finset.range (Nat.min N₁ N₂)), T i
  -- use triangle inequality: ‖A - B‖ ≤ ‖A‖ + ‖B‖
  -- and bound each by the sum of per-term flat norms.
  have hAB : prefixSum (n := n) (X := X) (k := k) T N₁ - prefixSum (n := n) (X := X) (k := k) T N₂ = A - B := by
    -- unfold A,B and use the decomposition lemma
    simpa [A, B] using hdecomp
  rw [hAB]
  have htri :
      _root_.flatNorm (n := n) (X := X) (k := k) (A - B) ≤
        _root_.flatNorm (n := n) (X := X) (k := k) A +
          _root_.flatNorm (n := n) (X := X) (k := k) B := by
    -- `A - B = A + (-B)` and use `flatNorm_add_le` + `flatNorm_neg`
    have : _root_.flatNorm (n := n) (X := X) (k := k) (A - B)
        ≤ _root_.flatNorm (n := n) (X := X) (k := k) A +
            _root_.flatNorm (n := n) (X := X) (k := k) (-B) := by
      simpa [sub_eq_add_neg] using
        (_root_.flatNorm_add_le (n := n) (X := X) (k := k) A (-B))
    -- rewrite `flatNorm (-B) = flatNorm B`
    simpa using this.trans_eq (by simp [_root_.flatNorm_neg (n := n) (X := X) (k := k) B])
  refine le_trans htri ?_
  -- bound each tail by sum of per-term flat norms
  have hA :
      _root_.flatNorm (n := n) (X := X) (k := k) A ≤
        ∑ i ∈ (Finset.range N₁ \ Finset.range (Nat.min N₁ N₂)),
          _root_.flatNorm (n := n) (X := X) (k := k) (T i) := by
    -- `A` is a finset sum by definition
    simpa [A] using
      (flatNorm_sum_le_sum_flatNorm (n := n) (X := X) (k := k)
        (s := (Finset.range N₁ \ Finset.range (Nat.min N₁ N₂))) (T := fun i => T i))
  have hB :
      _root_.flatNorm (n := n) (X := X) (k := k) B ≤
        ∑ i ∈ (Finset.range N₂ \ Finset.range (Nat.min N₁ N₂)),
          _root_.flatNorm (n := n) (X := X) (k := k) (T i) := by
    simpa [B] using
      (flatNorm_sum_le_sum_flatNorm (n := n) (X := X) (k := k)
        (s := (Finset.range N₂ \ Finset.range (Nat.min N₁ N₂))) (T := fun i => T i))
  exact add_le_add hA hB

end Hodge.TexSpine.TemplateFlat
