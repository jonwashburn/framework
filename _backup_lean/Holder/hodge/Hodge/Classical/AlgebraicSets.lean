import Hodge.Basic
import Hodge.Cohomology.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Topology.Constructions
import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Algebraic sets on projective complex manifolds (real semantics)

This file defines **algebraic subsets** as pullbacks of **homogeneous polynomial zero loci**
along the projective embedding bundled in `ProjectiveComplexManifold`.

Key points:
- We use the repo’s internal `ProjSpace` model from `Hodge/Basic.lean` (a quotient of nonzero
  vectors by scaling), since Mathlib’s `Projectivization` modules are not precompiled in the
  Mathlib cache used here.
- We do **not** define “algebraic set := IsClosed”. Closedness is proved from continuity.
- No axioms/sorries/opaque: this is concrete syntax and topology over `ℂ`.
-/

noncomputable section

open Classical
open scoped BigOperators

set_option autoImplicit false

universe u

namespace Hodge
namespace AlgGeom

/-! `ProjSpace` lives in the root namespace (defined in `Hodge/Basic.lean`).  We re-alias it here
so unqualified names work nicely inside `Hodge.AlgGeom`. -/
abbrev ProjVec (N : ℕ) := _root_.ProjVec N
abbrev ProjVecNZ (N : ℕ) := _root_.ProjVecNZ N
abbrev ProjSpace (N : ℕ) := _root_.ProjSpace N

/-! ## Homogeneous polynomials on projective space -/

/-- The (total) degree of a monomial exponent vector. -/
def monomialDegree {σ : Type*} (m : σ →₀ ℕ) : ℕ :=
  ∑ i ∈ m.support, m i

/-- A multivariate polynomial is homogeneous of degree `d` if all its monomials have total degree `d`.

We define this locally (rather than using Mathlib’s `MvPolynomial.IsHomogeneous`) to avoid relying on
un-cached Mathlib modules. -/
def IsHomogeneous {σ : Type*} (φ : MvPolynomial σ ℂ) (d : ℕ) : Prop :=
  ∀ m : σ →₀ ℕ, φ.coeff m ≠ 0 → monomialDegree m = d

/-- The zero polynomial is homogeneous of any degree. -/
theorem IsHomogeneous_zero {σ : Type*} (d : ℕ) : IsHomogeneous (0 : MvPolynomial σ ℂ) d := by
  intro m hm
  -- No coefficients of the zero polynomial are nonzero.
  exfalso
  simpa using hm

/-- The constant polynomial `1` is homogeneous of degree 0. -/
theorem IsHomogeneous_one {σ : Type*} [DecidableEq σ] : IsHomogeneous (1 : MvPolynomial σ ℂ) 0 := by
  intro m hm
  -- `coeff m 1` is nonzero only for `m = 0`.
  have hm0 : m = 0 := by
    by_contra h
    have h0 : (0 : σ →₀ ℕ) ≠ m := by simpa [eq_comm] using h
    have : (MvPolynomial.coeff m (1 : MvPolynomial σ ℂ)) = 0 := by
      simp [MvPolynomial.coeff_one, h0]
    exact hm this
  subst hm0
  simp [monomialDegree]

/-- The variable `X i` is homogeneous of degree 1. -/
theorem IsHomogeneous_X {σ : Type*} [DecidableEq σ] (i : σ) :
    IsHomogeneous (MvPolynomial.X i : MvPolynomial σ ℂ) 1 := by
  classical
  intro m hm
  -- `coeff m (X i)` is nonzero only for `m = single i 1`.
  have hm' : m = Finsupp.single i 1 := by
    by_contra hne
    have hne' : ¬Finsupp.single i 1 = m := by simpa [eq_comm] using hne
    have : (MvPolynomial.coeff m (MvPolynomial.X i : MvPolynomial σ ℂ)) = 0 := by
      simp [MvPolynomial.coeff_X', hne']
    exact hm this
  subst hm'
  -- Compute the total degree.
  simp [monomialDegree, Finsupp.support_single_ne_zero]

/-! ## Homogeneity is preserved by multiplication -/

private lemma exists_ne_zero_of_sum_ne_zero {α β : Type*} [DecidableEq α] [AddCommMonoid β]
    {s : Finset α} {f : α → β} (h : s.sum f ≠ 0) :
    ∃ a ∈ s, f a ≠ 0 := by
  classical
  -- Generalize over `s` to run induction.
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro hsum
    exfalso
    simpa using hsum
  · intro a s ha ih hsum
    by_cases hfa : f a = 0
    · have hsum' : s.sum f ≠ 0 := by
        simpa [Finset.sum_insert, ha, hfa] using hsum
      rcases ih hsum' with ⟨b, hb, hbne⟩
      exact ⟨b, Finset.mem_insert_of_mem hb, hbne⟩
    · exact ⟨a, Finset.mem_insert_self _ _, hfa⟩

/-- Additivity of `monomialDegree` for `ℕ`-valued finsupps. -/
lemma monomialDegree_add {σ : Type*} [DecidableEq σ] (a b : σ →₀ ℕ) :
    monomialDegree (a + b) = monomialDegree a + monomialDegree b := by
  classical
  -- `support (a + b) = support a ∪ support b` for ℕ-valued finsupps (no cancellation).
  have hsupport : (a + b).support = a.support ∪ b.support := by
    ext i; constructor
    · intro hi
      have h : a i + b i ≠ 0 := by
        simpa [Finsupp.mem_support_iff] using hi
      by_cases ha : a i = 0
      · have hb : b i ≠ 0 := by
          intro hb
          exact h (by simp [ha, hb])
        exact Finset.mem_union.mpr (Or.inr ((Finsupp.mem_support_iff).2 hb))
      · exact Finset.mem_union.mpr (Or.inl ((Finsupp.mem_support_iff).2 ha))
    · intro hi
      rcases Finset.mem_union.1 hi with ha | hb
      · have ha' : a i ≠ 0 := (Finsupp.mem_support_iff).1 ha
        have hsum : a i + b i ≠ 0 := by
          intro hzero
          have hz := (Nat.add_eq_zero_iff).1 hzero
          exact ha' hz.1
        exact (Finsupp.mem_support_iff).2 hsum
      · have hb' : b i ≠ 0 := (Finsupp.mem_support_iff).1 hb
        have hsum : a i + b i ≠ 0 := by
          intro hzero
          have hz := (Nat.add_eq_zero_iff).1 hzero
          exact hb' hz.2
        exact (Finsupp.mem_support_iff).2 hsum
  -- Now compute the sum over the union.
  unfold monomialDegree
  rw [hsupport]
  -- Expand the sum over the union and split.
  calc
    ∑ i ∈ a.support ∪ b.support, (a + b) i
        = ∑ i ∈ a.support ∪ b.support, (a i + b i) := by
            simp [Finsupp.add_apply]
    _ = (∑ i ∈ a.support ∪ b.support, a i) + (∑ i ∈ a.support ∪ b.support, b i) := by
            simp [Finset.sum_add_distrib]
  -- Restrict each sum to the appropriate support.
  have hsum_a :
      (∑ i ∈ a.support ∪ b.support, a i) = ∑ i ∈ a.support, a i := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro i hi
      exact Finset.mem_union.mpr (Or.inl hi)
    · intro i _ hnot
      by_contra h
      exact hnot ((Finsupp.mem_support_iff).2 h)
  have hsum_b :
      (∑ i ∈ a.support ∪ b.support, b i) = ∑ i ∈ b.support, b i := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro i hi
      exact Finset.mem_union.mpr (Or.inr hi)
    · intro i _ hnot
      by_contra h
      exact hnot ((Finsupp.mem_support_iff).2 h)
  simp [hsum_a, hsum_b]

/-- Homogeneity is preserved under multiplication. -/
theorem IsHomogeneous.mul {σ : Type*} [DecidableEq σ]
    {φ ψ : MvPolynomial σ ℂ} {d₁ d₂ : ℕ}
    (hφ : IsHomogeneous φ d₁) (hψ : IsHomogeneous ψ d₂) :
    IsHomogeneous (φ * ψ) (d₁ + d₂) := by
  classical
  intro n hn
  -- Use the coefficient formula for products.
  have hsum :
      (∑ x ∈ Finset.antidiagonal n, MvPolynomial.coeff x.1 φ * MvPolynomial.coeff x.2 ψ) ≠ 0 := by
    simpa [MvPolynomial.coeff_mul] using hn
  obtain ⟨x, hx, hxne⟩ := exists_ne_zero_of_sum_ne_zero (s := Finset.antidiagonal n) hsum
  have hx1 : MvPolynomial.coeff x.1 φ ≠ 0 := by
    intro h0
    exact hxne (by simp [h0])
  have hx2 : MvPolynomial.coeff x.2 ψ ≠ 0 := by
    intro h0
    exact hxne (by simp [h0])
  have hdeg1 : monomialDegree x.1 = d₁ := hφ _ hx1
  have hdeg2 : monomialDegree x.2 = d₂ := hψ _ hx2
  -- Antidiagonal membership gives `x.1 + x.2 = n`.
  have hxsum : x.1 + x.2 = n := by
    simpa using (Finset.mem_antidiagonal.mp hx)
  -- Combine degrees.
  calc
    monomialDegree n = monomialDegree (x.1 + x.2) := by simpa [hxsum]
    _ = monomialDegree x.1 + monomialDegree x.2 := monomialDegree_add _ _
    _ = d₁ + d₂ := by simp [hdeg1, hdeg2]

/-- A homogeneous polynomial on `ℙ^N(ℂ)` (represented by an `MvPolynomial` plus a homogeneity proof). -/
structure HomogeneousPolynomial (N : ℕ) where
  degree : ℕ
  poly : MvPolynomial (Fin (N + 1)) ℂ
  isHomogeneous : IsHomogeneous poly degree

namespace HomogeneousPolynomial

variable {N : ℕ}

@[simp] def eval (P : HomogeneousPolynomial N) (v : ProjVec N) : ℂ :=
  P.poly.eval v

/-- The homogeneous degree-1 coordinate polynomial `X i`. Its projective vanishing locus is a hyperplane. -/
def coord (i : Fin (N + 1)) : HomogeneousPolynomial N :=
  { degree := 1
    poly := MvPolynomial.X i
    isHomogeneous := IsHomogeneous_X (σ := Fin (N + 1)) i }

@[simp] theorem eval_coord (i : Fin (N + 1)) (v : ProjVec N) :
    (coord (N := N) i).eval v = (MvPolynomial.X i).eval v := rfl

/-- Product of homogeneous polynomials (degree adds). -/
def mul (P Q : HomogeneousPolynomial N) : HomogeneousPolynomial N :=
  { degree := P.degree + Q.degree
    poly := P.poly * Q.poly
    isHomogeneous := IsHomogeneous.mul P.isHomogeneous Q.isHomogeneous }

@[simp] theorem eval_mul (P Q : HomogeneousPolynomial N) (v : ProjVec N) :
    (mul P Q).eval v = P.eval v * Q.eval v := by
  simp [mul, HomogeneousPolynomial.eval, MvPolynomial.eval_mul]

/-- The constant homogeneous polynomial `1` of degree `0`. -/
def one (N : ℕ) : HomogeneousPolynomial N :=
  { degree := 0
    poly := 1
    isHomogeneous := IsHomogeneous_one }

@[simp] theorem eval_one (v : ProjVec N) : (one N).eval v = 1 := by
  simp [one, HomogeneousPolynomial.eval]

end HomogeneousPolynomial

/-! ## Scaling lemma for homogeneous polynomials -/

namespace MvPolynomial

variable {N : ℕ}

/-- If `φ` is homogeneous of degree `d`, then evaluating at `t • x` scales by `t^d`. -/
theorem IsHomogeneous.eval_smul {d : ℕ} (φ : MvPolynomial (Fin (N + 1)) ℂ) (hφ : IsHomogeneous φ d)
    (t : ℂ) (x : Fin (N + 1) → ℂ) :
    φ.eval (t • x) = (t ^ d) * φ.eval x := by
  classical
  -- Expand both sides using the `support`-sum formula.
  simp only [MvPolynomial.eval_eq, Finset.mul_sum]
  -- Prove termwise that each monomial picks up a factor `t^d`.
  refine Finset.sum_congr rfl ?_
  intro m hm
  have hcoeff : φ.coeff m ≠ 0 := (_root_.MvPolynomial.mem_support_iff).1 hm
  have hdeg : monomialDegree m = d := hφ m hcoeff
  -- Separate the `t` factors inside the product.
  have hprod :
      (∏ i ∈ m.support, (t • x) i ^ m i) =
        (t ^ d) * (∏ i ∈ m.support, x i ^ m i) := by
    -- `t • x` is pointwise multiplication in `ℂ`.
    have :
        (∏ i ∈ m.support, (t * x i) ^ m i) =
          (t ^ (∑ i ∈ m.support, m i)) * (∏ i ∈ m.support, x i ^ m i) := by
      -- Expand `(t * x i) ^ m i` and factor the `t` powers.
      calc
        (∏ i ∈ m.support, (t * x i) ^ m i)
            = (∏ i ∈ m.support, (t ^ m i) * (x i ^ m i)) := by
                refine Finset.prod_congr rfl ?_
                intro i hi
                simpa [mul_pow] using (mul_pow t (x i) (m i))
        _ = (∏ i ∈ m.support, t ^ m i) * (∏ i ∈ m.support, x i ^ m i) := by
              simp [Finset.prod_mul_distrib]
        _ = (t ^ (∑ i ∈ m.support, m i)) * (∏ i ∈ m.support, x i ^ m i) := by
              simp [Finset.prod_pow_eq_pow_sum, mul_assoc]
    -- Replace the exponent sum by `degree m`, then by `d`.
    have hsum : (∑ i ∈ m.support, m i) = d := by simpa [monomialDegree] using hdeg
    -- Finish.
    simpa [Pi.smul_apply, smul_eq_mul, hsum] using this
  -- Assemble the scaled term and factor out `t^d`.
  calc
    φ.coeff m * (∏ i ∈ m.support, (t • x) i ^ m i)
        = φ.coeff m * ((t ^ d) * (∏ i ∈ m.support, x i ^ m i)) := by
            -- Avoid simp-canceling `φ.coeff m`; apply `congrArg` to the proven product identity.
            exact congrArg (fun z => φ.coeff m * z) hprod
    _ = (t ^ d) * (φ.coeff m * (∏ i ∈ m.support, x i ^ m i)) := by ring_nf

end MvPolynomial

/-! ## Projective vanishing predicate -/

namespace HomogeneousPolynomial

variable {N : ℕ}

/-- A homogeneous polynomial vanishes at a projective point iff it vanishes on (equivalently: on any)
nonzero representative. -/
noncomputable def projVanishes (P : HomogeneousPolynomial N) : ProjSpace N → Prop :=
  Quotient.lift
    (fun v : ProjVecNZ N => P.eval v.1 = 0)
    (by
      intro v w hvw
      rcases hvw with ⟨t, ht, hv⟩
      -- Use the homogeneity scaling relation at the representative level.
      have hscale :
          P.eval v.1 = (t ^ P.degree) * P.eval w.1 := by
        -- rewrite `v.1` as `t • w.1`
        have : v.1 = t • w.1 := hv
        -- apply the scaling lemma
        simpa [HomogeneousPolynomial.eval, this] using
          (MvPolynomial.IsHomogeneous.eval_smul (N := N) (φ := P.poly) (d := P.degree)
            P.isHomogeneous t w.1)
      -- `t^deg ≠ 0` since `t ≠ 0`
      have htdeg : (t ^ P.degree : ℂ) ≠ 0 := pow_ne_zero _ ht
      -- Convert to equality of Props via Iff.
      apply propext
      constructor
      · intro hv0
        have hmul : (t ^ P.degree : ℂ) * P.eval w.1 = 0 := by
          -- from `hscale.symm : (t^deg)*eval(w) = eval(v)` and `hv0 : eval(v)=0`
          calc
            (t ^ P.degree : ℂ) * P.eval w.1 = P.eval v.1 := hscale.symm
            _ = 0 := hv0
        have h_or : (t ^ P.degree : ℂ) = 0 ∨ P.eval w.1 = 0 := mul_eq_zero.mp hmul
        cases h_or with
        | inl htd =>
            exact (htdeg htd).elim
        | inr hw0 =>
            exact hw0
      · intro hw0
        -- `eval(v) = (t^deg)*eval(w) = 0` using `hw0`
        calc
          P.eval v.1 = (t ^ P.degree) * P.eval w.1 := hscale
          _ = (t ^ P.degree) * 0 := by
                -- rewrite using the hypothesis `hw0 : P.eval w.1 = 0`
                rw [hw0]
          _ = 0 := by simp
    )

@[simp] theorem projVanishes_mk (P : HomogeneousPolynomial N) (v : ProjVecNZ N) :
    projVanishes P (Quotient.mk' (s := _root_.projSetoid N) v) = (P.eval v.1 = 0) := rfl

/-- Vanishing of a product is equivalent to vanishing of one factor. -/
theorem projVanishes_mul (P Q : HomogeneousPolynomial N) (x : ProjSpace N) :
    projVanishes (mul P Q) x ↔ projVanishes P x ∨ projVanishes Q x := by
  classical
  refine Quotient.inductionOn x ?_
  intro v
  -- Reduce to a representative and use `mul_eq_zero`.
  simp [HomogeneousPolynomial.projVanishes, HomogeneousPolynomial.mul, HomogeneousPolynomial.eval,
    MvPolynomial.eval_mul, mul_eq_zero]

@[simp] theorem projVanishes_one (x : ProjSpace N) : ¬ projVanishes (one N) x := by
  classical
  refine Quotient.inductionOn x ?_
  intro v
  simp [HomogeneousPolynomial.projVanishes, HomogeneousPolynomial.one, HomogeneousPolynomial.eval]

end HomogeneousPolynomial

/-! ## Topology: projective zero loci are closed -/

namespace HomogeneousPolynomial

variable {N : ℕ}

open Topology

private theorem continuous_eval (p : MvPolynomial (Fin (N + 1)) ℂ) :
    Continuous (fun x : ProjVec N => p.eval x) := by
  -- This is the lemma `MvPolynomial.continuous_eval` from Mathlib, reproved here
  -- to avoid depending on an un-cached Mathlib module.
  simpa using (by
    -- `continuity` knows evaluation is built from ring operations.
    continuity : Continuous fun x : ProjVec N => MvPolynomial.eval x p)

/-- The projective vanishing locus `{x | P.projVanishes x}` is closed in `ProjSpace N`. -/
theorem isClosed_projVanishes (P : HomogeneousPolynomial N) :
    IsClosed {x : ProjSpace N | HomogeneousPolynomial.projVanishes P x} := by
  classical
  -- Use the quotient-map characterization of closed sets.
  let π : ProjVecNZ N → ProjSpace N := Quotient.mk' (s := _root_.projSetoid N)
  have hq : IsQuotientMap π := by
    simpa [π] using (isQuotientMap_quotient_mk' (X := ProjVecNZ N) (s := _root_.projSetoid N))
  -- It suffices to show the preimage under `π` is closed.
  have hpre :
      IsClosed (π ⁻¹' {x : ProjSpace N | HomogeneousPolynomial.projVanishes P x}) := by
    -- This preimage is exactly `{v | P.eval v.1 = 0}`.
    have :
        (π ⁻¹' {x : ProjSpace N | HomogeneousPolynomial.projVanishes P x}) =
          {v : ProjVecNZ N | P.eval v.1 = 0} := by
      ext v
      simp [π, HomogeneousPolynomial.projVanishes_mk]
    -- Preimage of a closed singleton under a continuous function.
    have hcont : Continuous (fun v : ProjVecNZ N => P.eval v.1) :=
      (continuous_eval (N := N) P.poly).comp continuous_subtype_val
    simpa [this] using (isClosed_singleton.preimage hcont)
  -- Push closedness down to the quotient.
  exact (Topology.IsQuotientMap.isClosed_preimage hq).1 hpre

end HomogeneousPolynomial

/-! ## Algebraic subsets of a projective complex manifold -/

/-- A set `Z ⊆ X` is algebraic if it is the pullback of a projective homogeneous polynomial
common zero locus along the fixed projective embedding `X → ℙ^N(ℂ)`. -/
def IsAlgebraicSet (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [P : ProjectiveComplexManifold n X] [K : KahlerManifold n X]
    (Z : Set X) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι)
    (F : ι → HomogeneousPolynomial (ProjectiveComplexManifold.embedding_dim (n := n) (X := X))),
      Z = {x : X | ∀ i, HomogeneousPolynomial.projVanishes (F i) (P.embedding x)}

/-- The whole space is algebraic (empty intersection). -/
theorem IsAlgebraicSet_univ (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [P : ProjectiveComplexManifold n X] [K : KahlerManifold n X] :
    IsAlgebraicSet n X (Set.univ : Set X) := by
  classical
  refine ⟨PEmpty, inferInstance, (fun i => nomatch i), ?_⟩
  ext x
  simp

/-- The empty set is algebraic (zero locus of the constant `1`). -/
theorem IsAlgebraicSet_empty (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [P : ProjectiveComplexManifold n X] [K : KahlerManifold n X] :
    IsAlgebraicSet n X (∅ : Set X) := by
  classical
  refine ⟨PUnit, inferInstance, (fun _ => HomogeneousPolynomial.one _), ?_⟩
  ext x
  constructor
  · intro hx
    cases hx
  · intro hx
    have hx' := hx PUnit.unit
    exact (HomogeneousPolynomial.projVanishes_one (x := P.embedding x)) hx'

/-- Intersections of algebraic sets are algebraic. -/
theorem IsAlgebraicSet_inter (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [P : ProjectiveComplexManifold n X] [K : KahlerManifold n X]
    (S T : Set X) :
    IsAlgebraicSet n X S → IsAlgebraicSet n X T → IsAlgebraicSet n X (S ∩ T) := by
  classical
  rintro ⟨ι, _hι, F, rfl⟩ ⟨κ, _hκ, G, rfl⟩
  refine ⟨Sum ι κ, inferInstance, ?_, ?_⟩
  · intro s
    cases s with
    | inl i => exact F i
    | inr j => exact G j
  · ext x; constructor
    · intro hx
      -- `hx` is membership in the intersection; unpack into the two components.
      have hx' :
          (∀ i, HomogeneousPolynomial.projVanishes (F i) (P.embedding x)) ∧
            (∀ j, HomogeneousPolynomial.projVanishes (G j) (P.embedding x)) := by
        simpa using hx
      intro s
      cases s with
      | inl i => exact hx'.1 i
      | inr j => exact hx'.2 j
    · intro hx
      -- Build the intersection witnesses from the `Sum`-indexed vanishing.
      have hxF : ∀ i, HomogeneousPolynomial.projVanishes (F i) (P.embedding x) := by
        intro i; exact hx (Sum.inl i)
      have hxG : ∀ j, HomogeneousPolynomial.projVanishes (G j) (P.embedding x) := by
        intro j; exact hx (Sum.inr j)
      exact ⟨hxF, hxG⟩

/-- Unions of algebraic sets are algebraic. -/
theorem IsAlgebraicSet_union (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [P : ProjectiveComplexManifold n X] [K : KahlerManifold n X]
    (S T : Set X) :
    IsAlgebraicSet n X S → IsAlgebraicSet n X T → IsAlgebraicSet n X (S ∪ T) := by
  classical
  rintro ⟨ι, _hι, F, rfl⟩ ⟨κ, _hκ, G, rfl⟩
  let H : ι × κ → HomogeneousPolynomial (P.embedding_dim) :=
    fun p => HomogeneousPolynomial.mul (F p.1) (G p.2)
  refine ⟨ι × κ, inferInstance, H, ?_⟩
  ext x; constructor
  · intro hx
    -- `hx` is membership in the union; unpack the `∨`.
    have hx' :
        (∀ i, HomogeneousPolynomial.projVanishes (F i) (P.embedding x)) ∨
          (∀ j, HomogeneousPolynomial.projVanishes (G j) (P.embedding x)) := by
      simpa using hx
    cases hx' with
    | inl hF =>
        -- If all `F i` vanish, every product vanishes.
        intro ⟨i, j⟩
        exact (HomogeneousPolynomial.projVanishes_mul (F i) (G j) (P.embedding x)).2 (Or.inl (hF i))
    | inr hG =>
        intro ⟨i, j⟩
        exact (HomogeneousPolynomial.projVanishes_mul (F i) (G j) (P.embedding x)).2 (Or.inr (hG j))
  · intro hx
    -- Use classical choice to decide which side vanishes.
    by_cases hF : ∀ i, HomogeneousPolynomial.projVanishes (F i) (P.embedding x)
    · exact Or.inl hF
    · have hnot : ∃ i, ¬ HomogeneousPolynomial.projVanishes (F i) (P.embedding x) := by
        simpa [not_forall] using hF
      rcases hnot with ⟨i, hi⟩
      have hG : ∀ j, HomogeneousPolynomial.projVanishes (G j) (P.embedding x) := by
        intro j
        have hprod := hx (i, j)
        have h_or :=
          (HomogeneousPolynomial.projVanishes_mul (F i) (G j) (P.embedding x)).1 hprod
        cases h_or with
        | inl hFi => exact (hi hFi).elim
        | inr hGj => exact hGj
      exact Or.inr hG

/-- Algebraic sets are closed. -/
theorem IsAlgebraicSet_isClosed (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [P : ProjectiveComplexManifold n X] [K : KahlerManifold n X]
    (S : Set X) : IsAlgebraicSet n X S → IsClosed S := by
  classical
  rintro ⟨ι, _hι, F, rfl⟩
  -- Each condition `projVanishes (F i) (P.embedding x)` defines a closed set in `X`.
  have hclosed_i : ∀ i : ι,
      IsClosed {x : X | HomogeneousPolynomial.projVanishes (F i) (P.embedding x)} := by
    intro i
    have : IsClosed {y : ProjSpace (P.embedding_dim) | HomogeneousPolynomial.projVanishes (F i) y} :=
      HomogeneousPolynomial.isClosed_projVanishes (N := P.embedding_dim) (F i)
    exact this.preimage P.embedding_continuous
  -- Intersections of closed sets are closed.
  -- `{x | ∀ i, ...}` is an intersection over `i`.
  simpa [Set.setOf_forall] using isClosed_iInter hclosed_i

end AlgGeom
end Hodge
