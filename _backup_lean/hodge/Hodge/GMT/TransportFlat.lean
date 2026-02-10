import Hodge.Analytic.FlatNorm

/-!
# Transport / Matching ⇒ Flat-Norm Control (TeX: `prop:transport-flat-glue-weighted`)

This file contains **purely formal** (i.e. non-analytic, non-geometric) lemmas that turn:

- per-piece flat decompositions with controlled cost, and
- a finite matching (permutation) of indices

into a bound on the flat norm of the total mismatch current.

These statements are the Lean backbone of the TeX estimate
`𝔽(B_F) ≤ inf_σ ∑ ‖u_a - u'_{σ(a)}‖ (Mass(Σ(u_a)) + Mass(∂Σ(u_a)))`,
once the geometric input “translate two slice currents and control the fill” is provided.
-/

noncomputable section

open Classical

namespace Hodge.TexSpine.TransportFlat

universe u

variable {n : ℕ} {X : Type u}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]
  [Nonempty X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

open Hodge.FlatNormFinite

/-! ## Finite matching bound -/

/-- **Piecewise decomposition ⇒ flat-norm bound on the total mismatch**.

Given a family of currents `T i` (think: per-index mismatch terms) and, for each `i`,
some decomposition `T i = S i + ∂R i` with `mass(S i) + mass(R i) ≤ cost i`,
then the flat norm of the finite sum is bounded by the sum of the costs.

This is the formal content used in TeX Proposition `prop:transport-flat-glue-weighted`
after producing each pairwise decomposition.
-/
theorem flatNorm_finSum_le_of_piecewise_decomp {k : ℕ} (N : ℕ)
    (T : Fin N → Current n X k) (cost : Fin N → ℝ)
    (hdecomp :
      ∀ i,
        ∃ (S : Current n X k) (R : Current n X (k + 1)),
          T i = S + Current.boundary R ∧ Current.mass S + Current.mass R ≤ cost i) :
    _root_.flatNorm (n := n) (X := X) (k := k) (finSum (n := n) (X := X) (k := k) N T)
      ≤ finSumℝ N cost := by
  -- First bound each term by its cost, via the definition of flat norm as an infimum over decompositions.
  have hterm : ∀ i, _root_.flatNorm (n := n) (X := X) (k := k) (T i) ≤ cost i := by
    intro i
    rcases hdecomp i with ⟨S, R, hT, hcost⟩
    exact
      flatNorm_le_of_exists_decomp_le (n := n) (X := X) (k := k) (T := T i) (c := cost i)
        ⟨S, R, hT, hcost⟩
  -- Then sum using the (recursion-based) finite-sum triangle inequality.
  exact flatNorm_finSum_le_of_forall (n := n) (X := X) (k := k) N T cost hterm

/-- **Permutation-matched mismatch ⇒ flat-norm bound**.

Given two families of currents `Sigma` and `Sigma'` indexed by `Fin N` and a permutation `σ`,
assume that for each index `i` we can bound the flat norm of the difference
`Sigma i - Sigma' (σ i)` by a cost `cost i`. Then the mismatch current

`B := ∑ i (Sigma i - Sigma' (σ i))`

has `flatNorm B ≤ ∑ i cost i`.
-/
theorem flatNorm_mismatch_le_of_perm {k : ℕ} (N : ℕ)
    (Sigma Sigma' : Fin N → Current n X k) (σ : Equiv.Perm (Fin N)) (cost : Fin N → ℝ)
    (hdecomp :
      ∀ i,
        ∃ (S : Current n X k) (R : Current n X (k + 1)),
          (Sigma i - Sigma' (σ i)) = S + Current.boundary R ∧ Current.mass S + Current.mass R ≤ cost i) :
    _root_.flatNorm (n := n) (X := X) (k := k)
        (finSum (n := n) (X := X) (k := k) N (fun i => Sigma i - Sigma' (σ i)))
      ≤ finSumℝ N cost :=
  flatNorm_finSum_le_of_piecewise_decomp (n := n) (X := X) (k := k) N
    (T := fun i => Sigma i - Sigma' (σ i)) (cost := cost) hdecomp

end Hodge.TexSpine.TransportFlat
