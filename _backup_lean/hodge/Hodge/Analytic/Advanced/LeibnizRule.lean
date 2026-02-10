import Hodge.Analytic.Advanced.ContMDiffForms
import Hodge.Analytic.DomCoprodComplex
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.GroupTheory.Perm.Fin

/-!
# Leibniz Rule for Exterior Derivative

This file provides the infrastructure to prove the graded Leibniz rule:
  d(ω ∧ η) = dω ∧ η + (-1)^k ω ∧ dη

## Main results

* `hasFDerivAt_wedge`: Derivative of wedge product of functions
* `mfderiv_wedge_apply`: Manifold derivative of wedge product
* `alternatizeUncurryFin_wedge_right`: Alternatization commutes with wedge (right fixed)
* `alternatizeUncurryFin_wedge_left`: Alternatization commutes with wedge (left fixed, with sign)
* `extDerivAt_wedge`: Exterior derivative of wedge product (the Leibniz rule)

## Implementation notes

The graded sign (-1)^k arises from the fact that `alternatizeUncurryFin` inserts the
derivative direction at the first index, while the wedge product naturally combines
indices from both forms. Moving the derivative index past k indices of a k-form
introduces the sign.
-/

open Manifold Set Filter
open scoped BigOperators TensorProduct

variable {n k : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]

namespace LeibnizRule

/-!
We work with complex-valued forms on a real-smooth manifold. Accordingly:

- fiber objects are `ℝ`-linear alternating maps with codomain `ℂ` (i.e. `FiberAlt n k`);
- the wedge product is `ContinuousAlternatingMap.wedgeℂ` (on a real vector space, with `ℂ` codomain).
-/

/-- Local alias used throughout this file: the fiber alternating maps are `FiberAlt`. -/
abbrev Alt (n k : ℕ) := FiberAlt n k

/-! ### Finite permutation bookkeeping

We will need explicit control over the sign of the “block swap” permutation on `Fin (k + l)` that
moves the last `l` coordinates in front of the first `k` coordinates.

Concretely, this permutation is a `k`-step rotation, so its sign is \((-1)^{k\cdot l}\).
-/

private lemma sign_finRotate' (N : ℕ) : Equiv.Perm.sign (finRotate N) = (-1 : ℤˣ) ^ (N - 1) := by
  cases N with
  | zero =>
    -- `finRotate 0 = 1`
    simp [finRotate]
  | succ n =>
    -- `finRotate (n+1)` has sign `(-1)^n`
    simpa [Nat.succ_sub_one] using (sign_finRotate n)

private lemma sign_finRotate_pow (N k : ℕ) :
    Equiv.Perm.sign ((finRotate N) ^ k) = (Equiv.Perm.sign (finRotate N)) ^ k := by
  -- `Equiv.Perm.sign` is a monoid hom, so it preserves powers
  simpa using map_pow (Equiv.Perm.sign) (finRotate N) k

/-- The `k`-step rotation on `Fin (k+l)` has sign `(-1)^(k*l)`. -/
private lemma sign_blockSwap (k l : ℕ) :
    Equiv.Perm.sign ((finRotate (k + l)) ^ k) = (-1 : ℤˣ) ^ (k * l) := by
  -- Compute sign via `sign_finRotate` and the fact that `k*(k-1)` is even.
  have h1 :
      Equiv.Perm.sign ((finRotate (k + l)) ^ k) =
        (Equiv.Perm.sign (finRotate (k + l))) ^ k := by
    simpa using sign_finRotate_pow (N := k + l) (k := k)
  -- Reduce to a pure `(-1)`-power identity in `ℤˣ`.
  rw [h1, sign_finRotate']
  -- Turn `(((-1)^(N-1))^k)` into `(-1)^((N-1)*k)`.
  rw [← pow_mul]
  cases k with
  | zero =>
    simp
  | succ k' =>
    -- Simplify the exponents `k+l-1` and `k*l` for `k = k'+1`.
    simp [Nat.succ_add]  -- turns `k'+1 + l - 1` into `k' + l` and `k*l` into `(k'+1)*l`
    -- Goal is now: `(-1) ^ ((k' + l) * (k' + 1)) = (-1) ^ ((k' + 1) * l)`.
    -- Rewrite `(k'+l)*(k'+1)` as `(k'+1)*l + (k'+1)*k'`, then kill the even term.
    have hk : (k' + l) * (k' + 1) = (k' + 1) * l + (k' + 1) * k' := by
      calc
        (k' + l) * (k' + 1) = (k' + 1) * (k' + l) := by simpa [Nat.mul_comm]
        _ = (k' + 1) * k' + (k' + 1) * l := by simp [Nat.mul_add]
        _ = (k' + 1) * l + (k' + 1) * k' := by ac_rfl
    rw [hk, pow_add]
    have hEven : Even ((k' + 1) * k') := Nat.even_mul_pred_self (k' + 1)
    rcases hEven with ⟨t, ht⟩
    have hkill : ((-1 : ℤˣ) ^ ((k' + 1) * k')) = 1 := by
      -- rewrite exponent as `2 * t`
      rw [ht, (two_mul t).symm, pow_mul]
      simp
    -- Cancel the extra factor.
    have hkill' : ((-1 : ℤˣ) ^ (k' * (k' + 1))) = 1 := by
      simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hkill
    simp [hkill', mul_assoc, mul_left_comm, mul_comm]

/-! ### Rotation powers and block-swap permutation signs -/

private lemma finRotate_pow_val (N k : ℕ) (i : Fin N) :
    (↑(((finRotate N) ^ k) i) : ℕ) = (↑i + k) % N := by
  cases N with
  | zero =>
    exact i.elim0
  | succ N =>
    -- Induct on `k`, generalizing the input index.
    induction k generalizing i with
    | zero =>
      simp [Nat.mod_eq_of_lt i.isLt]
    | succ k ih =>
      -- `(σ^(k+1)) i = (σ^k) (σ i)` and `finRotate` is `(+1)`
      have hstep : (finRotate (N + 1)) i = i + 1 := finRotate_succ_apply i
      -- Rewrite one step and use the IH.
      -- We work at the level of `.val` to avoid typeclass issues with `Fin + ℕ`.
      calc
        (↑(((finRotate (N + 1)) ^ (k + 1)) i) : ℕ)
            = (↑(((finRotate (N + 1)) ^ k) ((finRotate (N + 1)) i)) : ℕ) := by
                simp [pow_succ, Equiv.Perm.mul_apply]
        _ = (↑(((finRotate (N + 1)) ^ k) (i + 1)) : ℕ) := by simpa [hstep]
        _ = (↑(i + 1) + k) % (N + 1) := ih (i := i + 1)
        _ = ((↑i + 1) % (N + 1) + k) % (N + 1) := by
              simp [Fin.val_add]
        _ = (↑i + (k + 1)) % (N + 1) := by
              -- normalize modular arithmetic
              simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.add_mod, Nat.mod_mod]

/-! ### Block swap equivalence on `Fin (k+l)` -/

private noncomputable def blockSwapEquiv (k l : ℕ) : Fin (k + l) ≃ Fin (l + k) :=
  ((finSumFinEquiv (m := k) (n := l)).symm.trans (Equiv.sumComm (Fin k) (Fin l))).trans
    (finSumFinEquiv (m := l) (n := k))

private noncomputable def blockSwapPerm (k l : ℕ) : Equiv.Perm (Fin (k + l)) :=
  (blockSwapEquiv k l).trans (finCongr (Nat.add_comm l k))

private lemma blockSwapPerm_apply_left {k l : ℕ} (i : Fin k) :
    blockSwapPerm k l (finSumFinEquiv (Sum.inl i)) =
      (finCongr (Nat.add_comm l k)) (finSumFinEquiv (m := l) (n := k) (Sum.inr i)) := by
  simp [blockSwapPerm, blockSwapEquiv, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]

private lemma blockSwapPerm_apply_right {k l : ℕ} (j : Fin l) :
    blockSwapPerm k l (finSumFinEquiv (Sum.inr j)) =
      (finCongr (Nat.add_comm l k)) (finSumFinEquiv (m := l) (n := k) (Sum.inl j)) := by
  simp [blockSwapPerm, blockSwapEquiv, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]

private lemma blockSwapPerm_eq_finRotate_pow (k l : ℕ) :
    blockSwapPerm k l = (finRotate (k + l)) ^ l := by
  classical
  ext x
  -- Split `x : Fin (k+l)` into the left/right blocks using `finSumFinEquiv`.
  set s : Fin k ⊕ Fin l := (finSumFinEquiv (m := k) (n := l)).symm x
  have hx : finSumFinEquiv (m := k) (n := l) s = x := by
    simpa [s] using (Equiv.apply_symm_apply (finSumFinEquiv (m := k) (n := l)) x)
  -- Rewrite the goal at `x = finSumFinEquiv s`.
  rw [← hx]
  cases s with
  | inl i =>
    -- Compare values.
    have hL :
        blockSwapPerm k l (finSumFinEquiv (Sum.inl i)) =
          (finCongr (Nat.add_comm l k))
            (finSumFinEquiv (m := l) (n := k) (Sum.inr i)) := by
      simpa using (blockSwapPerm_apply_left (k := k) (l := l) i)
    have hlhs :
        (↑(blockSwapPerm k l (finSumFinEquiv (Sum.inl i))) : ℕ) = (↑i + l) := by
      have := congrArg (fun t : Fin (k + l) => (t : ℕ)) hL
      simpa [finCongr_apply, Fin.val_cast, finSumFinEquiv_apply_right, Fin.val_natAdd] using this
    have hrhs :
        (↑(((finRotate (k + l)) ^ l) (finSumFinEquiv (m := k) (n := l) (Sum.inl i))) : ℕ) =
          (↑i + l) % (k + l) := by
      simpa [finSumFinEquiv_apply_left, Fin.val_castAdd, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using
        (finRotate_pow_val (N := k + l) (k := l)
          (i := finSumFinEquiv (m := k) (n := l) (Sum.inl i)))
    rw [hlhs, hrhs]
    have hlt : (↑i + l) < k + l := by omega
    have hmod : (↑i + l) % (k + l) = ↑i + l := Nat.mod_eq_of_lt hlt
    simpa using hmod.symm
  | inr j =>
    have hL :
        blockSwapPerm k l (finSumFinEquiv (Sum.inr j)) =
          (finCongr (Nat.add_comm l k))
            (finSumFinEquiv (m := l) (n := k) (Sum.inl j)) := by
      simpa using (blockSwapPerm_apply_right (k := k) (l := l) j)
    have hlhs :
        (↑(blockSwapPerm k l (finSumFinEquiv (Sum.inr j))) : ℕ) = (↑j) := by
      have := congrArg (fun t : Fin (k + l) => (t : ℕ)) hL
      simpa [finCongr_apply, Fin.val_cast, finSumFinEquiv_apply_left, Fin.val_castAdd] using this
    have hrhs :
        (↑(((finRotate (k + l)) ^ l) (finSumFinEquiv (m := k) (n := l) (Sum.inr j))) : ℕ) =
          (k + (↑j) + l) % (k + l) := by
      simpa [finSumFinEquiv_apply_right, Fin.val_natAdd, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using
        (finRotate_pow_val (N := k + l) (k := l)
          (i := finSumFinEquiv (m := k) (n := l) (Sum.inr j)))
    rw [hlhs, hrhs]
    have hlt : (↑j) < k + l := by omega
    have hrewrite : k + (↑j) + l = (↑j) + (k + l) := by omega
    have hcalc : (k + (↑j) + l) % (k + l) = (↑j) := by
      calc
        (k + (↑j) + l) % (k + l) = ((↑j) + (k + l)) % (k + l) := by simpa [hrewrite]
        _ = (↑j) % (k + l) := by simpa using (Nat.add_mod_right (↑j) (k + l))
        _ = (↑j) := Nat.mod_eq_of_lt hlt
    simpa using hcalc.symm

private lemma sign_blockSwapPerm (k l : ℕ) :
    Equiv.Perm.sign (blockSwapPerm k l) = (-1 : ℤˣ) ^ (k * l) := by
  -- `blockSwapPerm k l` is rotation by `l` steps on `Fin (k+l)`.
  have hperm : blockSwapPerm k l = (finRotate (k + l)) ^ l := blockSwapPerm_eq_finRotate_pow k l
  -- Reduce to a pure `(-1)`-power identity in `ℤˣ`.
  have h1 :
      Equiv.Perm.sign ((finRotate (k + l)) ^ l) =
        (Equiv.Perm.sign (finRotate (k + l))) ^ l := by
    simpa using sign_finRotate_pow (N := k + l) (k := l)
  -- Now compute `sign (finRotate (k+l))` and simplify the exponent.
  rw [hperm, h1, sign_finRotate']
  -- Turn `(((-1)^(N-1))^l)` into `(-1)^((N-1)*l)`.
  rw [← pow_mul]
  cases l with
  | zero =>
    simp
  | succ l' =>
    -- Simplify the `N - 1` term with `N = k + (l' + 1)`.
    have hsub : k + (l' + 1) - 1 = k + l' := by omega
    rw [hsub]
    -- Goal: `(-1)^((k+l')*(l'+1)) = (-1)^(k*(l'+1))`.
    -- Rewrite `(k+l')*(l'+1)` as `(l'+1)*k + (l'+1)*l'`, then kill the even term.
    have hk : (k + l') * (l' + 1) = (l' + 1) * k + (l' + 1) * l' := by
      calc
        (k + l') * (l' + 1) = (l' + 1) * (k + l') := by simpa [Nat.mul_comm]
        _ = (l' + 1) * k + (l' + 1) * l' := by simp [Nat.mul_add]
        _ = (l' + 1) * k + (l' + 1) * l' := rfl
    -- Commute `(l'+1)*k` into `k*(l'+1)` and separate the even factor.
    have hk' : (k + l') * (l' + 1) = k * (l' + 1) + (l' + 1) * l' := by
      -- rearrange using commutativity
      calc
        (k + l') * (l' + 1) = (l' + 1) * k + (l' + 1) * l' := hk
        _ = k * (l' + 1) + (l' + 1) * l' := by ac_rfl
    rw [hk', pow_add]
    have hEven : Even ((l' + 1) * l') := Nat.even_mul_pred_self (l' + 1)
    rcases hEven with ⟨t, ht⟩
    have hkill : ((-1 : ℤˣ) ^ ((l' + 1) * l')) = 1 := by
      rw [ht, (two_mul t).symm, pow_mul]
      simp
    have hkill' : ((-1 : ℤˣ) ^ (l' * (l' + 1))) = 1 := by
      simpa [Nat.mul_comm] using hkill
    simp [hkill, hkill', mul_assoc, mul_left_comm, mul_comm]

private lemma blockSwapEquiv_symm_apply_left {k l : ℕ} (j : Fin l) :
    (blockSwapEquiv k l).symm (finSumFinEquiv (m := l) (n := k) (Sum.inl j)) =
      (finSumFinEquiv (m := k) (n := l)) (Sum.inr j) := by
  simp [blockSwapEquiv, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]

private lemma blockSwapEquiv_symm_apply_right {k l : ℕ} (i : Fin k) :
    (blockSwapEquiv k l).symm (finSumFinEquiv (m := l) (n := k) (Sum.inr i)) =
      (finSumFinEquiv (m := k) (n := l)) (Sum.inl i) := by
  simp [blockSwapEquiv, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]

private lemma blockSwapEquiv_symm_apply_swap {k l : ℕ} (x : Fin k ⊕ Fin l) :
    (blockSwapEquiv k l).symm (finSumFinEquiv (m := l) (n := k) (Sum.swap x)) =
      (finSumFinEquiv (m := k) (n := l)) x := by
  cases x with
  | inl i =>
    simpa using (blockSwapEquiv_symm_apply_right (k := k) (l := l) i)
  | inr j =>
    simpa using (blockSwapEquiv_symm_apply_left (k := k) (l := l) j)

private lemma permCongr_mul {α β : Type*} (e : α ≃ β) (σ τ : Equiv.Perm α) :
    e.permCongr (σ * τ) = e.permCongr σ * e.permCongr τ := by
  ext x
  simp [Equiv.permCongr_apply, Equiv.Perm.mul_apply]

private lemma permCongr_inv {α β : Type*} (e : α ≃ β) (σ : Equiv.Perm α) :
    e.permCongr σ⁻¹ = (e.permCongr σ)⁻¹ := by
  ext x
  apply (e.permCongr σ).injective
  simp [Equiv.permCongr_apply]

private lemma permCongr_sumComm_sumCongr {k l : ℕ}
    (σ : Equiv.Perm (Fin k)) (τ : Equiv.Perm (Fin l)) :
    (Equiv.sumComm (Fin k) (Fin l)).permCongr (Equiv.Perm.sumCongr σ τ) =
      Equiv.Perm.sumCongr τ σ := by
  ext x <;> cases x <;> simp [Equiv.permCongr_apply]

private lemma permCongr_symm {α β : Type*} (e : α ≃ β) (σ : Equiv.Perm α) :
    e.symm.permCongr (e.permCongr σ) = σ := by
  ext x
  simp [Equiv.permCongr_apply]

private lemma permCongr_symm' {α β : Type*} (e : α ≃ β) (σ : Equiv.Perm β) :
    e.permCongr (e.symm.permCongr σ) = σ := by
  ext x
  simp [Equiv.permCongr_apply]

private noncomputable def modSumCongrSwap (k l : ℕ) :
    Equiv.Perm.ModSumCongr (Fin k) (Fin l) ≃ Equiv.Perm.ModSumCongr (Fin l) (Fin k) := by
  classical
  let e := (Equiv.sumComm (Fin k) (Fin l))
  refine
    { toFun := ?f
      invFun := ?g
      left_inv := ?l
      right_inv := ?r }
  · intro q
    refine Quotient.map' (fun σ : Equiv.Perm (Fin k ⊕ Fin l) => e.permCongr σ) ?_ q
    intro σ τ h
    -- transport the left-relator through permCongr
    rw [QuotientGroup.leftRel_apply] at h
    rcases h with ⟨⟨sl, sr⟩, h⟩
    have h' : σ⁻¹ * τ = Equiv.Perm.sumCongr sl sr := by
      simpa [Equiv.Perm.sumCongrHom_apply] using h.symm
    apply (QuotientGroup.leftRel_apply).2
    refine ⟨⟨sr, sl⟩, ?_⟩
    have hswap :
        (e.permCongr σ)⁻¹ * (e.permCongr τ) = Equiv.Perm.sumCongr sr sl := by
      calc
        (e.permCongr σ)⁻¹ * (e.permCongr τ)
            = e.permCongr (σ⁻¹ * τ) := by
                simp [permCongr_mul, permCongr_inv]
        _ = e.permCongr (Equiv.Perm.sumCongr sl sr) := by simpa [h']
        _ = Equiv.Perm.sumCongr sr sl := by
              simpa using permCongr_sumComm_sumCongr (k := k) (l := l) sl sr
    simpa [Equiv.Perm.sumCongrHom_apply] using hswap.symm
  · intro q
    refine Quotient.map' (fun σ : Equiv.Perm (Fin l ⊕ Fin k) => e.symm.permCongr σ) ?_ q
    intro σ τ h
    rw [QuotientGroup.leftRel_apply] at h
    rcases h with ⟨⟨sl, sr⟩, h⟩
    have h' : σ⁻¹ * τ = Equiv.Perm.sumCongr sl sr := by
      simpa [Equiv.Perm.sumCongrHom_apply] using h.symm
    apply (QuotientGroup.leftRel_apply).2
    refine ⟨⟨sr, sl⟩, ?_⟩
    have hswap :
        (e.symm.permCongr σ)⁻¹ * (e.symm.permCongr τ) = Equiv.Perm.sumCongr sr sl := by
      calc
        (e.symm.permCongr σ)⁻¹ * (e.symm.permCongr τ)
            = e.symm.permCongr (σ⁻¹ * τ) := by
                simp [permCongr_mul, permCongr_inv]
        _ = e.symm.permCongr (Equiv.Perm.sumCongr sl sr) := by simpa [h']
        _ = Equiv.Perm.sumCongr sr sl := by
              simpa using
                (permCongr_sumComm_sumCongr (k := l) (l := k) sl sr)
    simpa [Equiv.Perm.sumCongrHom_apply] using hswap.symm
  · intro q
    refine Quotient.inductionOn' q ?_
    intro σ
    simp [Quotient.map'_mk'', permCongr_symm]
  · intro q
    refine Quotient.inductionOn' q ?_
    intro σ
    simp [Quotient.map'_mk'', permCongr_symm']

private lemma wedge_comm_domDomCongr {k l : ℕ} (A : Alt n k) (B : Alt n l) :
    ContinuousAlternatingMap.wedgeℂ (E := TangentModel n) A B =
      (ContinuousAlternatingMap.domDomCongr
        (ContinuousAlternatingMap.wedgeℂ (E := TangentModel n) B A) (blockSwapEquiv k l).symm) := by
  classical
  ext v
  simp [ContinuousAlternatingMap.wedgeℂ_apply,
    ContinuousAlternatingMap.wedgeℂ_linear,
    ContinuousAlternatingMap.domDomCongr_apply,
    AlternatingMap.domDomCongr_apply,
    LinearMap.compAlternatingMap_apply,
    AlternatingMap.domCoprod'_apply,
    AlternatingMap.domCoprod_apply,
    MultilinearMap.sum_apply]
  refine Fintype.sum_equiv (modSumCongrSwap k l)
      (fun a : Equiv.Perm.ModSumCongr (Fin k) (Fin l) =>
        (LinearMap.mul' ℝ ℂ)
          ((AlternatingMap.domCoprod.summand A.toAlternatingMap B.toAlternatingMap a)
            (v ∘ finSumFinEquiv)))
      (fun a : Equiv.Perm.ModSumCongr (Fin l) (Fin k) =>
        (LinearMap.mul' ℝ ℂ)
          ((AlternatingMap.domCoprod.summand B.toAlternatingMap A.toAlternatingMap a)
            ((v ∘ (blockSwapEquiv k l).symm) ∘ finSumFinEquiv)))
      ?_
  intro a
  refine Quotient.inductionOn' a ?_
  intro σ
  simp [modSumCongrSwap, Quotient.map'_mk'',
    AlternatingMap.domCoprod.summand_mk'',
    MultilinearMap.domDomCongr_apply,
    MultilinearMap.domCoprod_apply,
    blockSwapEquiv_symm_apply_swap,
    Equiv.permCongr_apply, permCongr_sumComm_sumCongr,
    LinearMap.mul'_apply, Function.comp_apply, mul_comm, mul_left_comm, mul_assoc]


/-! ### A `cycleRange`-based decomposition of `Perm (Fin (n+1))`

`Equiv.Perm.decomposeFin` decomposes a permutation using a single transposition `swap 0 p`,
so its sign contribution is `-1` (for `p ≠ 0`). For Leibniz-type identities we need the finer
`(-1)^p` factor, which is exactly the sign of the cycle `(0 1 ... p)` i.e. `Fin.cycleRange p`.

We package the standard trick:

Given `σ : Perm (Fin (n+1))`, let `p := σ 0` and set `σ' := p.cycleRange * σ`.
Then `σ' 0 = 0`, so `σ'` is determined by its restriction to `Fin n` (via successors).
Conversely, given `(p, e)` with `e : Perm (Fin n)`, we reconstruct
`σ := p.cycleRange.symm * decomposeFin.symm (0, e)`.

This normalization yields the clean sign identity
`sign σ = (-1)^p * sign e`.
-/

private noncomputable def decomposeFinCycleRange_toFun {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    Fin (n + 1) × Equiv.Perm (Fin n) :=
  let p : Fin (n + 1) := σ 0
  let σ' : Equiv.Perm (Fin (n + 1)) := p.cycleRange * σ
  (p, (Equiv.Perm.decomposeFin σ').2)

private noncomputable def decomposeFinCycleRange_invFun {n : ℕ} (pe : Fin (n + 1) × Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n + 1)) :=
  let p : Fin (n + 1) := pe.1
  let e : Equiv.Perm (Fin n) := pe.2
  p.cycleRange.symm * (Equiv.Perm.decomposeFin.symm (0, e))

private lemma decomposeFinCycleRange_left_inv {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    decomposeFinCycleRange_invFun (n := n) (decomposeFinCycleRange_toFun (n := n) σ) = σ := by
  classical
  -- Set up the normalization.
  set p : Fin (n + 1) := σ 0
  set σ' : Equiv.Perm (Fin (n + 1)) := p.cycleRange * σ
  have hσ'0 : σ' 0 = 0 := by
    simp [σ', p, Fin.cycleRange_self]
  -- Let `pe := decomposeFin σ'`. Since `σ' 0 = 0`, we have `pe.1 = 0`.
  set pe : Fin (n + 1) × Equiv.Perm (Fin n) := Equiv.Perm.decomposeFin σ' with hpe
  have hpe1 : pe.1 = 0 := by
    -- Turn `pe = decomposeFin σ'` into `decomposeFin.symm pe = σ'`.
    have hsymm : Equiv.Perm.decomposeFin.symm pe = σ' := by
      have := congrArg (Equiv.Perm.decomposeFin.symm) hpe
      -- RHS simplifies by `symm_apply_apply`.
      simpa using this
    have h0 := congrArg (fun τ => τ 0) hsymm
    -- Compute the LHS using `decomposeFin_symm_apply_zero` (after destructing `pe`).
    have hL : (Equiv.Perm.decomposeFin.symm pe) 0 = pe.1 := by
      rcases pe with ⟨p0, e0⟩
      simp [Equiv.Perm.decomposeFin_symm_apply_zero]
    -- Now `h0` becomes `pe.1 = σ' 0 = 0`.
    -- RHS is `σ' 0 = 0`.
    exact (hL.symm.trans h0).trans hσ'0
  have hpe0 : pe = (0, pe.2) := by
    ext <;> simp [hpe1]
  have hσ' : σ' = Equiv.Perm.decomposeFin.symm (0, pe.2) := by
    -- First show `decomposeFin σ' = (0, pe.2)`.
    have hdecomp : Equiv.Perm.decomposeFin σ' = (0, pe.2) := by
      -- `pe = decomposeFin σ'` by definition, and `pe = (0, pe.2)` from `hpe0`.
      exact hpe.symm.trans hpe0
    -- Apply `decomposeFin.symm` to both sides and simplify.
    have := congrArg (Equiv.Perm.decomposeFin.symm) hdecomp
    simpa using this
  -- Now cancel the normalization.
  -- invFun(toFun σ) = p.cycleRange.symm * σ' = σ.
  -- since `σ' = p.cycleRange * σ`.
  -- First rewrite `decomposeFin.symm (0, pe.2)` as `σ'`, then cancel.
  have hσ'symm : Equiv.Perm.decomposeFin.symm (0, pe.2) = σ' := hσ'.symm
  -- We avoid `simp` recursion by doing the cancellation explicitly.
  calc
    decomposeFinCycleRange_invFun (n := n) (decomposeFinCycleRange_toFun (n := n) σ)
        = p.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, pe.2) := by
            simp [decomposeFinCycleRange_toFun, decomposeFinCycleRange_invFun, p, σ', pe]
    _ = p.cycleRange.symm * σ' := by simpa [hσ'symm]
    _ = p.cycleRange.symm * (p.cycleRange * σ) := by simp [σ']
    _ = (p.cycleRange.symm * p.cycleRange) * σ := by
          simpa [mul_assoc] using (mul_assoc p.cycleRange.symm p.cycleRange σ).symm
    _ = σ := by simp

private lemma decomposeFinCycleRange_right_inv {n : ℕ} (pe : Fin (n + 1) × Equiv.Perm (Fin n)) :
    decomposeFinCycleRange_toFun (n := n) (decomposeFinCycleRange_invFun (n := n) pe) = pe := by
  classical
  rcases pe with ⟨p, e⟩
  -- Compute `toFun (invFun (p,e))`.
  ext
  · -- first component
    -- Unfold `toFun`: the first component is evaluation at `0`.
    simp [decomposeFinCycleRange_toFun, decomposeFinCycleRange_invFun, Equiv.Perm.mul_apply,
      Equiv.Perm.decomposeFin_symm_apply_zero, Fin.cycleRange_symm_zero]
  · -- second component
    -- The normalized permutation is exactly `decomposeFin.symm (0,e)`.
    have hnorm :
        p.cycleRange * (p.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, e)) =
          Equiv.Perm.decomposeFin.symm (0, e) := by
      -- cancel `p.cycleRange` with its inverse
      calc
        p.cycleRange * (p.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, e))
            = (p.cycleRange * p.cycleRange.symm) * Equiv.Perm.decomposeFin.symm (0, e) := by
              simpa [mul_assoc] using
                (mul_assoc p.cycleRange p.cycleRange.symm (Equiv.Perm.decomposeFin.symm (0, e))).symm
        _ = Equiv.Perm.decomposeFin.symm (0, e) := by simp
    -- Apply `decomposeFin` to both sides and take `Prod.snd`.
    have hdecomp :
        (Equiv.Perm.decomposeFin
            (p.cycleRange * (p.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, e)))).2 = e := by
      -- `decomposeFin (decomposeFin.symm (0,e)) = (0,e)`
      simpa [hnorm] using congrArg Prod.snd (Equiv.apply_symm_apply (Equiv.Perm.decomposeFin) (0, e))
    simpa [decomposeFinCycleRange_toFun, decomposeFinCycleRange_invFun, hdecomp]

private noncomputable def decomposeFinCycleRange {n : ℕ} :
    Equiv.Perm (Fin (n + 1)) ≃ Fin (n + 1) × Equiv.Perm (Fin n) :=
  ⟨decomposeFinCycleRange_toFun (n := n), decomposeFinCycleRange_invFun (n := n),
    decomposeFinCycleRange_left_inv (n := n), decomposeFinCycleRange_right_inv (n := n)⟩

private lemma decomposeFinCycleRange_symm_apply_zero {n : ℕ} (p : Fin (n + 1)) (e : Equiv.Perm (Fin n)) :
    (decomposeFinCycleRange (n := n)).symm (p, e) 0 = p := by
  classical
  simp [decomposeFinCycleRange, decomposeFinCycleRange_invFun, Fin.cycleRange_symm_zero]

private lemma decomposeFinCycleRange_symm_apply_succ {n : ℕ} (p : Fin (n + 1)) (e : Equiv.Perm (Fin n))
    (x : Fin n) :
    (decomposeFinCycleRange (n := n)).symm (p, e) x.succ = p.succAbove (e x) := by
  classical
  -- Use `decomposeFin_symm_apply_succ` with `p = 0`, then `cycleRange_symm_succ`.
  simp [decomposeFinCycleRange, decomposeFinCycleRange_invFun,
    Equiv.Perm.decomposeFin_symm_apply_succ, Fin.cycleRange_symm_succ]

private lemma decomposeFinCycleRange_symm_sign {n : ℕ} (p : Fin (n + 1)) (e : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign ((decomposeFinCycleRange (n := n)).symm (p, e)) =
      (-1 : ℤˣ) ^ (p : ℕ) * Equiv.Perm.sign e := by
  classical
  -- `sign` is a monoid hom; use `sign_mul`, `sign_inv`, `sign_cycleRange`,
  -- and `decomposeFin.symm_sign` at `p = 0`.
  simp [decomposeFinCycleRange, decomposeFinCycleRange_invFun,
    Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, Fin.sign_cycleRange, Equiv.Perm.decomposeFin.symm_sign]

/-! ### Derivative of Wedge Product -/

/-- The wedge product is a bounded bilinear map.
This is the key ingredient for computing derivatives of wedge products. -/
lemma isBoundedBilinearMap_wedge {k l : ℕ} :
    IsBoundedBilinearMap ℝ (fun p : Alt n k × Alt n l => ContinuousAlternatingMap.wedgeℂ (E := TangentModel n) p.1 p.2) where
  add_left := fun x₁ x₂ y => ContinuousAlternatingMap.wedgeℂ_add_left (E := TangentModel n) x₁ x₂ y
  smul_left := fun c x y => ContinuousAlternatingMap.wedgeℂ_smul_left (E := TangentModel n) (c := c) x y
  add_right := fun x y₁ y₂ => ContinuousAlternatingMap.wedgeℂ_add_right (E := TangentModel n) x y₁ y₂
  smul_right := fun c x y => ContinuousAlternatingMap.wedgeℂ_smul_right (E := TangentModel n) (c := c) x y
  bound := by
    -- The wedge is the composition of wedgeCLM_alt with function application
    -- wedgeCLM_alt : Alt k →L[ℂ] (Alt l →L[ℂ] Alt (k+l))
    -- So (ω, η) ↦ (wedgeCLM_alt ω) η is bounded bilinear
    let f := ContinuousAlternatingMap.wedgeℂCLM_alt (E := TangentModel n) k l
    -- Use that (g, x) ↦ g x for g : E →L F, x : E is bounded bilinear
    -- with bound max ‖f‖ 1
    have h := f.isBoundedBilinearMap
    obtain ⟨C, hC_pos, hC⟩ := h.bound
    exact ⟨C, hC_pos, hC⟩

/-- The derivative of the wedge product of two form-valued functions.

If `ω : G → Alt n k` and `η : G → Alt n l` are differentiable at x, then
`y ↦ ω(y) ∧ η(y)` is differentiable and its derivative is:
  `v ↦ (Dω(v)) ∧ η(x) + ω(x) ∧ (Dη(v))`
-/
theorem hasFDerivAt_wedge {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {k l : ℕ} {ω : G → Alt n k} {η : G → Alt n l} {x : G}
    {ω' : G →L[ℝ] Alt n k} {η' : G →L[ℝ] Alt n l}
    (hω : HasFDerivAt ω ω' x) (hη : HasFDerivAt η η' x) :
    HasFDerivAt (fun y => ContinuousAlternatingMap.wedgeℂ (E := TangentModel n) (ω y) (η y))
      (isBoundedBilinearMap_wedge.deriv (ω x, η x) ∘L (ω'.prod η')) x := by
  -- Use the bounded bilinear map derivative rule
  have hB := isBoundedBilinearMap_wedge (n := n) (k := k) (l := l)
  -- hB.hasFDerivAt gives: HasFDerivAt wedge (hB.deriv (a, b)) (a, b)
  -- where hB.deriv (a, b) (v₁, v₂) = a.wedge v₂ + v₁.wedge b
  have hBilin := hB.hasFDerivAt (ω x, η x)
  -- Compose with (ω, η) : G → Alt k × Alt l using the chain rule
  have hPair : HasFDerivAt (fun y => (ω y, η y)) (ω'.prod η') x := hω.prodMk hη
  exact hBilin.comp x hPair

-- This lemma’s proof is heavy on `mfderiv` simp/reduction, so we give it a larger
-- heartbeat budget to keep builds deterministic.
set_option maxHeartbeats 1000000
/-- The manifold derivative of a wedge product follows the Leibniz rule (pointwise).

**Proof strategy**: For `modelWithCornersSelf`, `mfderiv` reduces to `fderiv` in chart coordinates.
The bilinear chain rule for wedge (`hasFDerivAt_wedge`) then gives the Leibniz formula.

The technical details involve:
1. Expressing mfderiv as fderivWithin on range I = univ (hence fderiv)
2. Identifying extChartAt with chartAt for modelWithCornersSelf
3. Applying hasFDerivAt_wedge to the chart representations
4. Relating fderiv of chart representation back to mfderiv -/
theorem mfderiv_wedge_apply {k l : ℕ} (ω : ContMDiffForm n X k) (η : ContMDiffForm n X l) (x : X)
    (v : TangentSpace (𝓒_complex n) x) :
    mfderiv (𝓒_complex n) 𝓘(ℝ, Alt n (k + l)) (ω.wedge η).as_alternating x v =
    ContinuousAlternatingMap.wedgeℂ (E := TangentModel n)
        (mfderiv (𝓒_complex n) 𝓘(ℝ, Alt n k) ω.as_alternating x v) (η.as_alternating x) +
      ContinuousAlternatingMap.wedgeℂ (E := TangentModel n)
        (ω.as_alternating x) (mfderiv (𝓒_complex n) 𝓘(ℝ, Alt n l) η.as_alternating x v) := by
  -- The wedge of ContMDiffForms has as_alternating = fun x => ω(x) ∧ η(x)
  have h_eq :
      (ω.wedge η).as_alternating =
        fun y => ContinuousAlternatingMap.wedgeℂ (E := TangentModel n) (ω.as_alternating y) (η.as_alternating y) :=
    rfl
  rw [h_eq]

  -- Step 1: Get differentiability hypotheses
  have hω_diff : MDifferentiableAt (𝓒_complex n) 𝓘(ℝ, Alt n k) ω.as_alternating x :=
    ω.smooth'.mdifferentiableAt (by simp : (⊤ : WithTop ℕ∞) ≠ 0)
  have hη_diff : MDifferentiableAt (𝓒_complex n) 𝓘(ℝ, Alt n l) η.as_alternating x :=
    η.smooth'.mdifferentiableAt (by simp : (⊤ : WithTop ℕ∞) ≠ 0)

  -- Step 2: Define the bilinear wedge map on the product
  let B : Alt n k × Alt n l → Alt n (k + l) :=
    fun p => ContinuousAlternatingMap.wedgeℂ (E := TangentModel n) p.1 p.2
  have hB : IsBoundedBilinearMap ℝ B := isBoundedBilinearMap_wedge (n := n) (k := k) (l := l)

  -- Step 3: The pair function
  let pair : X → Alt n k × Alt n l := fun y => (ω.as_alternating y, η.as_alternating y)

  -- Step 4: Show the pair is differentiable
  have hpair_diff : MDifferentiableAt (𝓒_complex n) 𝓘(ℝ, Alt n k × Alt n l) pair x :=
    hω_diff.prodMk_space hη_diff

  -- Step 5: B is smooth (as a map between real normed spaces)
  have hB_contDiff : ContDiff ℝ ⊤ B := hB.contDiff
  have hB_diff : DifferentiableAt ℝ B (pair x) :=
    hB_contDiff.differentiable (by simp : (⊤ : WithTop ℕ∞) ≠ 0) (pair x)

  -- Step 6: The function is B ∘ pair
  have h_comp : (fun y => ContinuousAlternatingMap.wedgeℂ (E := TangentModel n) (ω.as_alternating y) (η.as_alternating y)) =
      B ∘ pair := rfl

  -- Step 7: Apply the chain rule for mfderiv
  rw [h_comp]
  rw [mfderiv_comp x hB_diff.mdifferentiableAt hpair_diff]

  -- Step 8: Simplify mfderiv of B using mfderiv_eq_fderiv (source is a vector space)
  have h_mfderiv_B : mfderiv 𝓘(ℝ, Alt n k × Alt n l) 𝓘(ℝ, Alt n (k + l)) B (pair x) =
      fderiv ℝ B (pair x) := mfderiv_eq_fderiv

  -- Step 9: Get fderiv of bilinear map
  have h_fderiv_B : fderiv ℝ B (pair x) = hB.deriv (pair x) := hB.hasFDerivAt (pair x) |>.fderiv

  -- Step 10: Simplify mfderiv of pair using mfderiv_prodMk
  -- Use modelWithCornersSelf_prod and chartedSpaceSelf_prod to unify types
  have h_mfderiv_pair : mfderiv (𝓒_complex n) 𝓘(ℝ, Alt n k × Alt n l) pair x =
      (mfderiv (𝓒_complex n) 𝓘(ℝ, Alt n k) ω.as_alternating x).prod
        (mfderiv (𝓒_complex n) 𝓘(ℝ, Alt n l) η.as_alternating x) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact mfderiv_prodMk hω_diff hη_diff

  -- Step 11: Compute the final form
  simp only [h_mfderiv_B, h_fderiv_B, h_mfderiv_pair, IsBoundedBilinearMap.deriv, pair]
  show (hB.toContinuousLinearMap.deriv₂ (ω.as_alternating x, η.as_alternating x))
       ((mfderiv (𝓒_complex n) 𝓘(ℝ, Alt n k) ω.as_alternating x v,
         mfderiv (𝓒_complex n) 𝓘(ℝ, Alt n l) η.as_alternating x v)) =
       ContinuousAlternatingMap.wedgeℂ (E := TangentModel n)
          (mfderiv (𝓒_complex n) 𝓘(ℝ, Alt n k) ω.as_alternating x v) (η.as_alternating x) +
       ContinuousAlternatingMap.wedgeℂ (E := TangentModel n)
          (ω.as_alternating x) (mfderiv (𝓒_complex n) 𝓘(ℝ, Alt n l) η.as_alternating x v)
  -- Apply coe_deriv₂
  simp only [ContinuousLinearMap.coe_deriv₂]
  -- Goal: `ω ∧ (Dη v) + (Dω v) ∧ η = (Dω v) ∧ η + ω ∧ (Dη v)`
  -- These are equal by `add_comm`.
  exact add_comm _ _

-- Restore the default heartbeat budget for the rest of the file.
set_option maxHeartbeats 200000

/-! ### Alternatization and Wedge Compatibility

These two lemmas are the core combinatorial identities needed for the Leibniz rule.
They relate the sum structure of `alternatizeUncurryFin` (sum over derivative indices)
with the sum structure of `wedge` (sum over shuffles via `domCoprod`).

The proofs require showing that a double sum over (derivative index, shuffles) can be
reindexed to match the structure on the other side. This is a classical identity in
the theory of graded derivations on exterior algebras.

**Mathematical content**: Both identities express that `d` (exterior derivative) is a
graded derivation, meaning `d(ω ∧ η) = dω ∧ η + (-1)^deg(ω) ω ∧ dη`.
-/

/-! #### Helper lemmas for wedge product distribution -/

/-- Wedge with zero on the left gives zero. -/
private lemma wedge_zero_left' {k l : ℕ} (B : Alt n l) : (0 : Alt n k).wedgeℂ B = 0 := by
  ext v
  simp [ContinuousAlternatingMap.wedgeℂ_apply, ContinuousAlternatingMap.wedgeℂ_linear]

/-- Wedge distributes over finite sums in the left argument. -/
private lemma wedge_sum_left {k l : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Alt n k) (B : Alt n l) (s : Finset ι) :
    (∑ i ∈ s, f i).wedgeℂ B = ∑ i ∈ s, (f i).wedgeℂ B := by
  induction s using Finset.induction_on with
  | empty => simp [wedge_zero_left']
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    -- Expand the wedge of a sum, then use the induction hypothesis.
    -- (Avoid `simpa` here: simp can rewrite the goal into a form where the term is seen as `True`.)
    have h :=
      ContinuousAlternatingMap.wedgeℂ_add_left (E := TangentModel n) (ω₁ := f a) (ω₂ := ∑ i ∈ s, f i) (η := B)
    -- `h` has the desired shape after rewriting the `Finset.sum_insert`.
    -- Now finish by rewriting the tail using `ih`.
    -- Note: the remaining goal is exactly `h` with the tail rewritten.
    simpa [h, ih, add_assoc, add_left_comm, add_comm]

/-- Wedge distributes over finite sums (Fintype version). -/
private lemma wedge_finsum_left {k l : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Alt n k) (B : Alt n l) :
    (∑ i, f i).wedgeℂ B = ∑ i, (f i).wedgeℂ B := by
  convert wedge_sum_left f B Finset.univ <;> simp

/-- Wedge is compatible with integer scalar multiplication on the left. -/
private lemma wedge_zsmul_left {k l : ℕ} (c : ℤ) (ω : Alt n k) (B : Alt n l) :
    (c • ω).wedgeℂ B = c • (ω.wedgeℂ B) := by
  -- Fix the right argument; wedge is an `ℝ`-linear (hence `ℤ`-linear) map in the left argument.
  let L : Alt n k →L[ℝ] Alt n (k + l) :=
    (ContinuousAlternatingMap.wedgeℂCLM_alt (E := TangentModel n) k l).flip B
  -- Rewrite both sides in terms of `L`, then apply `map_zsmul`.
  -- (Avoid `simp [L]`: it can trigger instance search for scalar actions on linear maps.)
  change L (c • ω) = c • L ω
  simpa using (map_zsmul L c ω)

/-- Wedge distributes over finite sums with integer scalars. -/
private lemma wedge_zsmul_finsum_left {k l : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι → ℤ) (f : ι → Alt n k) (B : Alt n l) :
    (∑ i, c i • f i).wedgeℂ B = ∑ i, c i • (f i).wedgeℂ B := by
  rw [wedge_finsum_left]
  congr 1
  ext i
  rw [wedge_zsmul_left]

/-! #### Helper lemma: `domCoprod` as full alternatization

Mathlib relates the shuffle-based `AlternatingMap.domCoprod` to the “full alternatization” of the
underlying multilinear `MultilinearMap.domCoprod`.  This is sometimes a more convenient form for
sum-reindexing arguments, because it replaces the quotient over shuffles by a sum over *all*
permutations (at the cost of a factorial scaling). -/

private lemma domCoprod_smul_factorial_eq_alternatization {k l : ℕ}
    (ω : Alt n k) (η : Alt n l) :
    (k.factorial * l.factorial) • (ω.toAlternatingMap.domCoprod η.toAlternatingMap) =
      MultilinearMap.alternatization
        ((ω.toAlternatingMap.toMultilinearMap).domCoprod (η.toAlternatingMap.toMultilinearMap)) := by
  -- This is `MultilinearMap.domCoprod_alternization_eq`, specialized to `Fin k`, `Fin l`, and `ℂ`.
  -- We write it in the “scaled domCoprod = alternatization” direction.
  -- Note: the scalar here is an `ℕ`-scalar (`nsmul`), exactly matching Mathlib's statement.
  simpa using
    (MultilinearMap.domCoprod_alternization_eq (a := ω.toAlternatingMap) (b := η.toAlternatingMap)).symm

private lemma domCoprod_eq_inv_factorial_smul_alternatization {k l : ℕ}
    (ω : Alt n k) (η : Alt n l) :
    ω.toAlternatingMap.domCoprod η.toAlternatingMap =
      (((k.factorial * l.factorial : ℕ) : ℂ)⁻¹) •
        MultilinearMap.alternatization
          ((ω.toAlternatingMap.toMultilinearMap).domCoprod (η.toAlternatingMap.toMultilinearMap)) := by
  classical
  -- Start from the `nsmul` (Nat-scalar) identity, then convert it to an `ℂ`-scalar identity and cancel.
  set m : ℕ := k.factorial * l.factorial
  have hNat :
      m • (ω.toAlternatingMap.domCoprod η.toAlternatingMap) =
        MultilinearMap.alternatization
          ((ω.toAlternatingMap.toMultilinearMap).domCoprod (η.toAlternatingMap.toMultilinearMap)) := by
    simpa [m] using
      (domCoprod_smul_factorial_eq_alternatization (n := n) (k := k) (l := l) ω η)
  have h :
      ((m : ℂ) • (ω.toAlternatingMap.domCoprod η.toAlternatingMap)) =
        MultilinearMap.alternatization
          ((ω.toAlternatingMap.toMultilinearMap).domCoprod (η.toAlternatingMap.toMultilinearMap)) := by
    -- Rewrite the Nat action as scalar multiplication by `(m : ℂ)`.
    -- `Nat.cast_smul_eq_nsmul` has the form `(↑m : ℂ) • x = m • x`.
    simpa [Nat.cast_smul_eq_nsmul] using hNat
  have hm : (m : ℂ) ≠ 0 := by
    -- `m = k! * l!` is a positive natural number.
    have hmNat : m ≠ 0 := by
      simp [m, Nat.mul_ne_zero, Nat.factorial_ne_zero]
    exact_mod_cast hmNat
  -- Multiply both sides by the inverse scalar and simplify.
  have h' := congrArg (fun z => ((m : ℂ)⁻¹) • z) h
  -- LHS simplifies by `inv_mul_cancel₀` + `smul_smul`.
  have hinv : (m : ℂ)⁻¹ * (m : ℂ) = 1 := inv_mul_cancel₀ hm
  -- Turn `((m⁻¹) • ((m) • x))` into `((m⁻¹*m) • x)` and cancel.
  simpa [smul_smul, hinv, one_smul] using h'

private lemma wedge_apply_eq_inv_factorial_smul_alternatization {k l : ℕ}
    (ω : Alt n k) (η : Alt n l) (v : Fin (k + l) → TangentModel n) :
    (ω.wedgeℂ η) v =
      (((k.factorial * l.factorial : ℕ) : ℂ)⁻¹) •
        (LinearMap.mul' ℝ ℂ)
          ((MultilinearMap.alternatization
              ((ω.toAlternatingMap.toMultilinearMap).domCoprod (η.toAlternatingMap.toMultilinearMap)))
            (v ∘ finSumFinEquiv)) := by
  classical
  -- Unfold the wedge definition down to `AlternatingMap.domCoprod`, then rewrite using the inverse-factorial lemma.
  simp only [ContinuousAlternatingMap.wedgeℂ_apply,
    ContinuousAlternatingMap.wedgeℂ_linear]
  simp only [AlternatingMap.domDomCongr_apply, LinearMap.compAlternatingMap_apply,
    AlternatingMap.domCoprod'_apply]
  -- Replace the shuffle-quotient `domCoprod` by the full alternatization sum.
  -- (We keep the result *before* expanding the alternatization sum.)
  rw [domCoprod_eq_inv_factorial_smul_alternatization (n := n) (k := k) (l := l) ω η]
  -- Pull the scalar out through the linear map `LinearMap.mul'`.
  -- The scalar `((k! * l! : ℕ) : ℂ)⁻¹` is a real number (cast to `ℂ`), so we can
  -- pull it out using ℝ-linearity of `LinearMap.mul'`.
  have hmNat : (k.factorial * l.factorial : ℕ) ≠ 0 := by
    simp [Nat.mul_ne_zero, Nat.factorial_ne_zero]
  have hmR : ((k.factorial * l.factorial : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hmNat
  have hmul : ((k.factorial * l.factorial : ℕ) : ℂ) * (((((k.factorial * l.factorial : ℕ) : ℝ)⁻¹ : ℝ)) : ℂ) = 1 := by
    -- reduce to ℝ
    norm_cast
    field_simp [hmR]
  have hinv : (((k.factorial * l.factorial : ℕ) : ℂ)⁻¹) =
      (((((k.factorial * l.factorial : ℕ) : ℝ)⁻¹ : ℝ)) : ℂ) :=
    inv_eq_of_mul_eq_one_right hmul
  -- Rewrite the scalar and use `map_smul` (ℝ-linearity).
  rw [hinv]
  -- Avoid `simp` trying to pull the scalar out as a *multiplication* in `ℂ`:
  -- we explicitly use the ℝ-linearity statement `map_smul`.
  -- (The scalar is a real number, viewed inside `ℂ`.)
  -- First rewrite the scalar-smul as an ℝ-smul.
  -- (This is definitional for the `ℝ`-module structure on `ℂ`.)
  -- Then apply `map_smul`.
  -- The goal is presented in terms of the product of the two factorial inverses.
  -- To use ℝ-linearity of `LinearMap.mul'`, we rewrite that scalar as the cast of the real inverse
  -- of the product `(k! * l!)`.
  -- Now finish by ℝ-linearity (the scalar is real, seen inside `ℂ`).
  -- We avoid `simpa` here (it can simplify the proof term’s type to `True` via `eq_self_iff_true`).
  -- Instead we rewrite the goal into an explicit `map_smul` instance.
  -- First, rewrite the scalar into the commuting product form.
  -- (This matches the normal form produced earlier by `domCoprod_eq_inv_factorial_smul_alternatization`.)
  -- After that, we rewrite the ℂ-scalar multiplication by the real inverse as an ℝ-scalar multiplication.
  -- Finally, we apply `map_smul` and re-associate multiplications.
  -- Abbreviation for the tensor-valued alternatization term.
  set t : (ℂ ⊗[ℝ] ℂ) :=
    (MultilinearMap.alternatization
        ((ω.toAlternatingMap.toMultilinearMap).domCoprod (η.toAlternatingMap.toMultilinearMap)))
      (v ∘ finSumFinEquiv)
  -- Replace the complex inverse scalar by the product-of-inverses form.
  -- (Both are in `ℂ`, but come from `ℕ`-casts, hence from `ℝ`.)
  -- Then treat the scalar as an `ℝ`-scalar and apply `map_smul`.
  -- We do this by changing the goal rather than relying on simp.
  -- Rewrite the scalar on the LHS.
  have hmap :
      (LinearMap.mul' ℝ ℂ) ((((k.factorial * l.factorial : ℕ) : ℝ)⁻¹) • t) =
        (((k.factorial * l.factorial : ℕ) : ℝ)⁻¹) • (LinearMap.mul' ℝ ℂ) t :=
    map_smul (LinearMap.mul' ℝ ℂ) (((k.factorial * l.factorial : ℕ) : ℝ)⁻¹) t
  -- Rewrite the complex scalar `(↑l.factorial)⁻¹ * (↑k.factorial)⁻¹` as the cast of the real inverse
  -- of `k.factorial * l.factorial`, so that `hmap` applies.
  have hscalar :
      (((l.factorial : ℕ) : ℂ)⁻¹ * ((k.factorial : ℕ) : ℂ)⁻¹) =
        (((((k.factorial * l.factorial : ℕ) : ℝ)⁻¹ : ℝ)) : ℂ) := by
    have hmNat : (k.factorial * l.factorial : ℕ) ≠ 0 := by
      simp [Nat.mul_ne_zero, Nat.factorial_ne_zero]
    have hmR : ((k.factorial * l.factorial : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast hmNat
    -- First identify `(k! * l! : ℂ)⁻¹` with the cast of the real inverse.
    have hmul' :
        ((k.factorial * l.factorial : ℕ) : ℂ) * (((((k.factorial * l.factorial : ℕ) : ℝ)⁻¹ : ℝ)) : ℂ) = 1 := by
      norm_cast
      field_simp [hmR]
    have hinv' :
        (((k.factorial * l.factorial : ℕ) : ℂ)⁻¹) =
          (((((k.factorial * l.factorial : ℕ) : ℝ)⁻¹ : ℝ)) : ℂ) :=
      inv_eq_of_mul_eq_one_right hmul'
    -- Now rewrite the LHS as `(k! * l! : ℂ)⁻¹` using commutativity.
    have hinv_mul' :
        (((k.factorial * l.factorial : ℕ) : ℂ)⁻¹) =
          ((l.factorial : ℕ) : ℂ)⁻¹ * ((k.factorial : ℕ) : ℂ)⁻¹ := by
      have : ((k.factorial * l.factorial : ℕ) : ℂ) =
          ((l.factorial : ℕ) : ℂ) * ((k.factorial : ℕ) : ℂ) := by
        norm_cast
        ring
      calc
        (((k.factorial * l.factorial : ℕ) : ℂ)⁻¹)
            = (((((l.factorial : ℕ) : ℂ) * ((k.factorial : ℕ) : ℂ)))⁻¹) := by simpa [this]
        _ = ((l.factorial : ℕ) : ℂ)⁻¹ * ((k.factorial : ℕ) : ℂ)⁻¹ := by
              simpa using (mul_inv (((l.factorial : ℕ) : ℂ)) (((k.factorial : ℕ) : ℂ)))
    -- Combine the two characterizations of the inverse.
    -- (We rewrite the LHS using `hinv_mul'` and then use `hinv'`.)
    calc
      (( (l.factorial : ℕ) : ℂ)⁻¹ * ((k.factorial : ℕ) : ℂ)⁻¹)
          = (((k.factorial * l.factorial : ℕ) : ℂ)⁻¹) := by
              simpa [hinv_mul'] using hinv_mul'.symm
      _ = (((((k.factorial * l.factorial : ℕ) : ℝ)⁻¹ : ℝ)) : ℂ) := hinv'
  -- Rewrite the goal using `hscalar`, then finish with `hmap`.
  -- We avoid `simp` here (it can loop on scalar-cast normalizations); instead we rewrite explicitly.
  -- 1) unfold `t` where it appears;
  -- 2) rewrite the scalar `(↑l.factorial)⁻¹ * (↑k.factorial)⁻¹` as the cast of the real inverse;
  -- 3) use `hmap`.
  -- Step 1: unfold `t` in the goal.
  -- (The `set` tactic introduced a definitional equation `t = _` that `simp`/`rw` can use.)
  -- We use `simp [t]` just to unfold `t` once.
  -- (No scalar rewriting here.)
  -- Step 2: rewrite scalars.
  -- Now the goal matches `hmap` (up to definitional equality of `((r : ℂ) • ·)` with `(r • ·)`).
  -- Step 3: exact `hmap`.
  -- Note: we may need `smul_smul` and `mul_assoc` to match the nested scalar action presentation.
  -- We do those rewrites explicitly.
  -- Rewrite the product-of-inverses scalar on both sides.
  -- (This converts the goal’s scalar to an `ℝ`-scalar, so `hmap` applies.)
  -- Finally, close with `hmap`.
  -- Unfold `t` in the goal.
  -- (Using `simp [t]` avoids having to reference the generated equation name.)
  -- Only simplify the *goal* (do not simplify hypotheses like `hscalar`, otherwise simp may turn them into `True`).
  simp [t]
  -- Rewrite scalar in the goal.
  rw [hscalar]
  -- Now close with `hmap`.
  -- `hmap` is exactly the statement that `LinearMap.mul'` commutes with the ℝ-scalar.
  -- Any remaining associativity is definitional for scalar multiplication on tensor products.
  -- At this point the goal is exactly `hmap` (up to definitional equality of scalar actions),
  -- so we can close directly without further simp-rewriting.
  exact hmap

/-! #### Core reindexing lemma for the right-constant Leibniz identity

This is the combinatorial heart of `shuffle_bijection_right` for `l > 0`, written at the level of
the “full alternatization” sums over permutations.

It expresses that (after clearing factorial scalars) the alternatization sum for
`(alternatizeUncurryFin A) ∧ B` can be rewritten as a signed sum over the removed index `x`,
matching the definition of `alternatizeUncurryFin`.
-/
set_option maxHeartbeats 800000

private lemma stage1_lemma {k l : ℕ} {n : ℕ}
    (w : (Fin (k + 1) ⊕ Fin l) → TangentModel n)
    (A : TangentModel n →L[ℝ] Alt n k)
    (B : Alt n l) :
    (∑ σ : Equiv.Perm (Fin (k + 1) ⊕ Fin l),
          ((Equiv.Perm.sign σ : ℤ) : ℂ) *
            ((ContinuousAlternatingMap.alternatizeUncurryFin (𝕜 := ℝ) (F := ℂ) A)
                (fun i : Fin (k + 1) => w (σ (Sum.inl i))) *
              B (fun j : Fin l => w (σ (Sum.inr j))))) =
      (k + 1 : ℂ) *
        ∑ σ : Equiv.Perm (Fin (k + 1) ⊕ Fin l),
          ((Equiv.Perm.sign σ : ℤ) : ℂ) *
            (A (w (σ (Sum.inl 0)))
                (fun i : Fin k => w (σ (Sum.inl i.succ))) *
              B (fun j : Fin l => w (σ (Sum.inr j)))) := by
  classical
  -- Helper abbreviations
  let left (σ : Equiv.Perm (Fin (k + 1) ⊕ Fin l)) : Fin (k + 1) → TangentModel n :=
    fun i => w (σ (Sum.inl i))
  let right (σ : Equiv.Perm (Fin (k + 1) ⊕ Fin l)) : Fin l → TangentModel n :=
    fun j => w (σ (Sum.inr j))

  -- Step 1: Expand alternatizeUncurryFin and distribute
  have hexpand : ∀ σ : Equiv.Perm (Fin (k + 1) ⊕ Fin l),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ((ContinuousAlternatingMap.alternatizeUncurryFin (𝕜 := ℝ) (F := ℂ) A) (left σ) * B (right σ)) =
      ∑ i : Fin (k + 1),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((-1 : ℂ) ^ (i : ℕ)) *
          (A (left σ i) (i.removeNth (left σ)) * B (right σ)) := by
    intro σ
    rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply]
    -- The apply gives: ∑ i, (-1)^i • A(left σ i)(removeNth i (left σ))
    -- Convert zsmul to ℂ multiplication
    have hzsmul : ∀ i : Fin (k + 1),
        ((-1 : ℤ) ^ (i : ℕ)) • A (left σ i) (i.removeNth (left σ)) =
        ((-1 : ℂ) ^ (i : ℕ)) * A (left σ i) (i.removeNth (left σ)) := by
      intro i
      rw [← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul]
      simp only [Int.cast_pow, Int.cast_neg, Int.cast_one]
    simp_rw [hzsmul]
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

  -- Apply expansion
  conv_lhs =>
    arg 2
    ext σ
    rw [hexpand σ]
  -- Step 2: Swap order of summation
  rw [Finset.sum_comm]

  -- Step 3-4: Show each inner sum (over σ) is the same for all i
  have hinner : ∀ i : Fin (k + 1),
      ∑ σ : Equiv.Perm (Fin (k + 1) ⊕ Fin l),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((-1 : ℂ) ^ (i : ℕ)) *
          (A (left σ i) (i.removeNth (left σ)) * B (right σ)) =
      ∑ σ : Equiv.Perm (Fin (k + 1) ⊕ Fin l),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) *
          (A (left σ 0) ((0 : Fin (k + 1)).removeNth (left σ)) * B (right σ)) := by
    intro i
    -- Define τ_i := sumCongr (cycleRange i) 1 (NOT the inverse!)
    -- Then σ ↦ τ * σ maps: σ(inl 0) → τ(σ(inl 0)), with τ(inl j) = inl (cycleRange i j)
    -- cycleRange i maps: 0 → 1 → 2 → ... → i → 0 (cycle)
    -- So τ * σ applied to inl 0 gives σ(inl (cycleRange i 0)) = σ(inl 1) if i ≥ 1
    -- Actually we want: σ(inl 0) → σ(inl i)
    -- Use σ ↦ σ * τ with τ = sumCongr (cycleRange i)⁻¹ 1, then
    -- (σ * τ)(inl 0) = σ(τ(inl 0)) = σ(inl ((cycleRange i)⁻¹ 0)) = σ(inl i)
    -- because cycleRange⁻¹ sends 0 to i.
    let τ : Equiv.Perm (Fin (k + 1) ⊕ Fin l) := Equiv.Perm.sumCongr i.cycleRange.symm 1
    -- sign(τ) = sign(cycleRange⁻¹) = sign(cycleRange) = (-1)^i
    have hsignτ : Equiv.Perm.sign τ = (-1 : ℤˣ) ^ (i : ℕ) := by
      simp only [τ, Equiv.Perm.sign_sumCongr, Equiv.Perm.sign_one, mul_one]
      conv_lhs => rw [show i.cycleRange.symm = i.cycleRange⁻¹ from rfl, Equiv.Perm.sign_inv]
      exact Fin.sign_cycleRange i
    have hsignτ' : (Equiv.Perm.sign τ : ℤ) = (-1 : ℤ) ^ (i : ℕ) := by
      simp only [hsignτ, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
    -- Fintype.sum_equiv e f g h shows: ∑_σ f(e σ) = ∑_σ g(σ) when h σ : f(e σ) = g σ
    -- We have:
    --   f(σ) = source = sign(σ) * (-1)^i * A(left σ i)...
    --   g(σ) = target = sign(σ) * A(left σ 0)...
    -- We want ∑ f = ∑ g, but sum_equiv gives ∑ f∘e = ∑ g
    -- Use symmetry: prove ∑ g = ∑ f, then apply symm
    -- For this, we need sum_equiv e' g f h' where g(e' σ) = f(σ)
    -- With e' = mulRight τ⁻¹, we get g(σ * τ⁻¹) = f(σ)
    -- i.e., sign(σ*τ⁻¹) * A(left(σ*τ⁻¹) 0)... = sign(σ) * (-1)^i * A(left σ i)...
    -- Using sign(τ⁻¹) = sign(τ) = (-1)^i and left(σ*τ⁻¹) 0 = σ(τ⁻¹(inl 0)) = σ(inl (cycleRange 0))
    -- cycleRange at 0 is cycleRange i applied to 0 gives... 1 (for i > 0) or 0 (for i = 0)
    -- This is getting complicated. Let me use the direct approach.
    --
    -- Direct approach: ∑ f = ∑ g by showing f(σ) = g(σ * τ) for the right τ
    -- f_i(σ) = sign(σ) * (-1)^i * A(left σ i)...
    -- g(σ') = sign(σ') * A(left σ' 0)...
    -- For σ' = σ * τ with τ = sumCongr cycleRange.symm 1:
    --   left σ' 0 = σ(τ(inl 0)) = σ(inl i) = left σ i
    --   sign(σ') = sign(σ) * (-1)^i
    -- So g(σ * τ) = sign(σ) * (-1)^i * A(left σ i)... = f_i(σ)
    -- Therefore ∑_σ f_i(σ) = ∑_σ g(σ * τ) = ∑_σ' g(σ') by bijection
    refine Fintype.sum_equiv (Equiv.mulRight τ) _ _ ?_
    intro σ
    -- Goal: f(σ) = g((mulRight τ) σ) = g(σ * τ)
    -- f(σ) = sign(σ) * (-1)^i * A(left σ i)...
    -- g(σ * τ) = sign(σ * τ) * A(left(σ*τ) 0)...
    -- Properties:
    have hsignστ : (Equiv.Perm.sign (σ * τ) : ℤ) =
          (Equiv.Perm.sign σ : ℤ) * (-1 : ℤ) ^ (i : ℕ) := by
      simp only [Equiv.Perm.sign_mul, hsignτ', Units.val_mul]
    -- (σ * τ)(inl 0) = σ(τ(inl 0)) = σ(inl (cycleRange i)⁻¹ 0) = σ(inl i)
    have hleft_i : left (σ * τ) 0 = left σ i := by
      simp only [left, τ, Equiv.Perm.mul_apply, Equiv.Perm.sumCongr_apply, Sum.map_inl,
        Fin.cycleRange_symm_zero]
    -- For x : Fin k, (σ * τ)(inl (succAbove 0 x)) = σ(τ(inl x.succ))
    -- τ(inl x.succ) = inl ((cycleRange i)⁻¹ x.succ) = inl (succAbove i ((cycleRange i)⁻¹.predAbove 0 x))
    -- Actually (cycleRange i)⁻¹ x.succ = succAbove i x (this is the key property!)
    have hremove : (0 : Fin (k + 1)).removeNth (left (σ * τ)) = i.removeNth (left σ) := by
      ext x
      simp only [left, τ, Fin.removeNth, Equiv.Perm.mul_apply, Equiv.Perm.sumCongr_apply,
        Sum.map_inl, Fin.succAbove_zero, Fin.cycleRange_symm_succ]
    have hright : right (σ * τ) = right σ := by
      ext j
      simp only [right, τ, Equiv.Perm.mul_apply, Equiv.Perm.sumCongr_apply, Sum.map_inr,
        Equiv.Perm.one_apply]
    -- Now combine
    -- The goal is: f(σ) = g((mulRight τ) σ) = g(σ * τ)
    -- f(σ) = sign(σ) * (-1)^i * A(left σ i)...
    -- g(σ * τ) = sign(σ * τ) * A(left(σ*τ) 0)...
    -- Using: sign(σ * τ) = sign(σ) * (-1)^i, left(σ*τ) 0 = left σ i, etc.
    have hmr : (Equiv.mulRight τ) σ = σ * τ := rfl
    simp only [hmr]
    -- Expand sign(σ * τ)
    rw [hsignστ, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
    -- Use the lemmas to show the terms match
    rw [hleft_i, hremove, hright]
    -- Goal is now reflexively true

  simp_rw [hinner]
  -- Step 5: The sum over i is (k+1) copies of the same thing
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul]
  -- Convert ↑(k + 1) to (↑k + 1) and unfold `left`, `right`
  simp only [Nat.cast_add, Nat.cast_one, left, right]
  -- The remaining difference: Fin.removeNth 0 f vs fun i => f i.succ
  -- Use: removeNth 0 f = fun i => f (succAbove 0 i) = fun i => f i.succ
  have hremNth : ∀ (f : Fin (k + 1) → TangentModel n),
      (Fin.removeNth 0 f) = (fun i : Fin k => f i.succ) := by
    intro f
    ext i
    simp only [Fin.removeNth, Fin.succAbove_zero]
  simp_rw [hremNth]

private lemma stage2_lemma {k l : ℕ}
    (v : Fin (k + l + 1) → TangentModel n)
    (A : TangentModel n →L[ℝ] Alt n k)
    (B : Alt n l) :
    let h : (k + 1) + l = (k + l) + 1 := by omega
    let w : (Fin (k + 1) ⊕ Fin l) → TangentModel n := (v ∘ finCongr h) ∘ finSumFinEquiv
    (∑ σ : Equiv.Perm (Fin (k + 1) ⊕ Fin l),
          ((Equiv.Perm.sign σ : ℤ) : ℂ) *
            (A (w (σ (Sum.inl 0)))
                (fun i : Fin k => w (σ (Sum.inl i.succ))) *
              B (fun j : Fin l => w (σ (Sum.inr j))))) =
    ∑ x : Fin (k + l + 1),
          ((-1 : ℂ) ^ (x : ℕ)) *
            (LinearMap.mul' ℝ ℂ)
              ((MultilinearMap.alternatization
                  ((A (v x)).toMultilinearMap.domCoprod B.toMultilinearMap))
                ((Fin.removeNth x v) ∘ finSumFinEquiv)) := by
  intro h w
  classical
  let equiv := (Equiv.permCongr ((finSumFinEquiv (m := k + 1) (n := l)).trans (finCongr h))).trans (decomposeFinCycleRange (n := k + l))

  let reindexed_term (p : Fin (k + l + 1) × Equiv.Perm (Fin (k + l))) : ℂ :=
    ((Equiv.Perm.sign (equiv.symm p) : ℤ) : ℂ) *
      (A (w (equiv.symm p (Sum.inl 0)))
          (fun i : Fin k => w (equiv.symm p (Sum.inl i.succ))) *
        B (fun j : Fin l => w (equiv.symm p (Sum.inr j))))

  trans ∑ p, reindexed_term p
  · refine Fintype.sum_equiv equiv _ _ ?_
    intro σ
    dsimp [reindexed_term]
    simp only [Equiv.symm_apply_apply]

  rw [Fintype.sum_prod_type]
  refine Fintype.sum_congr _ _ ?_
  intro x

  let M := ((A (v x)).toMultilinearMap.domCoprod B.toMultilinearMap)
  let u := (Fin.removeNth x v) ∘ finSumFinEquiv

  have hsign : ∀ e, ((Equiv.Perm.sign (equiv.symm (x, e)) : ℤ) : ℂ) =
               ((-1 : ℂ) ^ (x : ℕ)) * ((Equiv.Perm.sign e : ℤ) : ℂ) := by
     intro e
     simp [equiv, decomposeFinCycleRange_symm_sign, Equiv.Perm.sign_permCongr, mul_comm]

  dsimp [reindexed_term]
  simp_rw [hsign]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1

  -- Now show the inner reindexed sum agrees with the alternatization expansion.
  -- We rewrite the RHS alternatization sum over `Perm (Fin k ⊕ Fin l)` as a sum over `Perm (Fin (k+l))`
  -- using `finSumFinEquiv`, then match terms using the explicit formulas for `decomposeFinCycleRange.symm`.
  classical

  -- Some abbreviations: `f` is the domain equivalence used in `equiv`, and `g` is `finSumFinEquiv` for `(k,l)`.
  let f : (Fin (k + 1) ⊕ Fin l) ≃ Fin (k + l + 1) :=
    (finSumFinEquiv (m := k + 1) (n := l)).trans (finCongr h)
  let g : (Fin k ⊕ Fin l) ≃ Fin (k + l) :=
    finSumFinEquiv

  -- Expand RHS: alternatization is a sum over permutations; pull `mul'` inside the sum.
  -- Then reindex the permutation sum along `g.permCongr : Perm (Fin k ⊕ Fin l) ≃ Perm (Fin (k+l))`.
  have hrhs :
      (LinearMap.mul' ℝ ℂ)
          ((MultilinearMap.alternatization M) u) =
        ∑ e : Equiv.Perm (Fin (k + l)),
          ((Equiv.Perm.sign e : ℤ) : ℂ) *
            (A (v x)
                (fun i : Fin k =>
                  (Fin.removeNth x v) (e (g (Sum.inl i)))) *
              B (fun j : Fin l =>
                (Fin.removeNth x v) (e (g (Sum.inr j))))) := by
    classical
    -- `simp` expands `mul' (alternatization M) u` into a sum over permutations of `Fin k ⊕ Fin l`.
    simp [MultilinearMap.alternatization_apply]
    -- Reindex this sum to permutations of `Fin (k+l)` using `g`.
    refine Fintype.sum_equiv (Equiv.permCongr g)
        (fun σ : Equiv.Perm (Fin k ⊕ Fin l) =>
          Equiv.Perm.sign σ • (LinearMap.mul' ℝ ℂ) (M fun i => u (σ i)))
        (fun e : Equiv.Perm (Fin (k + l)) =>
          ((Equiv.Perm.sign e : ℤ) : ℂ) *
            (A (v x)
                (fun i : Fin k => (Fin.removeNth x v) (e (g (Sum.inl i)))) *
              B (fun j : Fin l => (Fin.removeNth x v) (e (g (Sum.inr j))))))
        ?_
    intro σ
    -- Let `e` be the transported permutation on `Fin (k+l)`.
    let e : Equiv.Perm (Fin (k + l)) := (Equiv.permCongr g) σ
    -- Sign is preserved under `permCongr`.
    have hsign :
        (Equiv.Perm.sign e : ℤ) = (Equiv.Perm.sign σ : ℤ) := by
      have hunit : Equiv.Perm.sign e = Equiv.Perm.sign σ := by
        simpa [e] using (Equiv.Perm.sign_permCongr (e := g) (p := σ))
      exact congrArg (fun u : ℤˣ => (u : ℤ)) hunit
    -- Compute the `mul'` of the domCoprod tensor and rewrite the inputs through `e`.
    have hmul :
        (LinearMap.mul' ℝ ℂ) (M fun i => u (σ i)) =
          (A (v x)
              (fun i : Fin k => (Fin.removeNth x v) (e (g (Sum.inl i)))) *
            B (fun j : Fin l => (Fin.removeNth x v) (e (g (Sum.inr j))))) := by
      -- First expand `M` and `u`.
      -- Then use `Equiv.permCongr_apply` to rewrite `e (g s)` as `g (σ s)`.
      have hginl : ∀ i : Fin k, finSumFinEquiv (σ (Sum.inl i)) = e (g (Sum.inl i)) := by
        intro i
        -- `e (g (inl i)) = g (σ (inl i))` by the definition of `permCongr`.
        simpa [g, e, Equiv.permCongr_apply]
      have hginr : ∀ j : Fin l, finSumFinEquiv (σ (Sum.inr j)) = e (g (Sum.inr j)) := by
        intro j
        simpa [g, e, Equiv.permCongr_apply]
      -- Now compute the tensor and apply `mul'`.
      simp [M, u, Function.comp_apply, MultilinearMap.domCoprod_apply, LinearMap.mul'_apply, hginl, hginr]
    -- Convert the `ℤˣ`-action on `ℂ` to multiplication by `((sign σ : ℤ) : ℂ)`.
    -- Then use sign invariance to replace it by `sign e`.
    simpa [e, Units.smul_def, zsmul_eq_mul, hsign, hmul, mul_assoc]

  -- It remains to identify the LHS inner sum with the explicit `hrhs` expression.
  -- We do this by rewriting the `w (equiv.symm (x,e) ...)` values using the explicit formulas
  -- for `decomposeFinCycleRange.symm`.
  -- First, rewrite `w` as `v ∘ f` and use `permCongr` evaluation.
  have hL0 : ∀ e : Equiv.Perm (Fin (k + l)),
      w (equiv.symm (x, e) (Sum.inl 0)) = v x := by
    intro e
    -- `equiv.symm (x,e)` is `(f.permCongr).symm ((decomposeFinCycleRange).symm (x,e))`.
    -- Applying `w = v ∘ f` reduces to evaluating that permutation on `0`.
    have hf0 : f (Sum.inl (0 : Fin (k + 1))) = (0 : Fin (k + l + 1)) := by
      -- Reduce to a value computation.
      apply Fin.ext
      simp [f, Equiv.trans_apply, finSumFinEquiv_apply_left, finCongr_apply]
    -- Now compute.
    simp [w, equiv, f, Equiv.trans_apply, Equiv.permCongr_symm_apply, hf0,
      decomposeFinCycleRange_symm_apply_zero]

  have hLs : ∀ (e : Equiv.Perm (Fin (k + l))) (i : Fin k),
      w (equiv.symm (x, e) (Sum.inl i.succ)) = (Fin.removeNth x v) (e (g (Sum.inl i))) := by
    intro e i
    -- Compute the index `f (inl i.succ)` as `succ (g (inl i))`.
    have hf_succ : f (Sum.inl i.succ) = (g (Sum.inl i)).succ := by
      apply Fin.ext
      -- Compare values.
      simp [f, g, Equiv.trans_apply, finSumFinEquiv_apply_left, finCongr_apply]
    -- Use the `decomposeFinCycleRange` formula on successors.
    simp [w, equiv, f, g, Equiv.trans_apply, Equiv.permCongr_symm_apply, hf_succ,
      decomposeFinCycleRange_symm_apply_succ, Fin.removeNth]

  have hR : ∀ (e : Equiv.Perm (Fin (k + l))) (j : Fin l),
      w (equiv.symm (x, e) (Sum.inr j)) = (Fin.removeNth x v) (e (g (Sum.inr j))) := by
    intro e j
    -- Compute the index `f (inr j)` as `succ (g (inr j))`.
    have hf_succ : f (Sum.inr j) = (g (Sum.inr j)).succ := by
      apply Fin.ext
      simp [f, g, Equiv.trans_apply, finSumFinEquiv_apply_right, finCongr_apply]
      omega
    simp [w, equiv, f, g, Equiv.trans_apply, Equiv.permCongr_symm_apply, hf_succ,
      decomposeFinCycleRange_symm_apply_succ, Fin.removeNth]

  -- Now rewrite the original LHS summand using these identities.
  -- This matches the RHS expression proven in `hrhs`.
  have hsum_match :
      (∑ e : Equiv.Perm (Fin (k + l)),
          ((Equiv.Perm.sign e : ℤ) : ℂ) *
            (A (w (equiv.symm (x, e) (Sum.inl 0)))
                (fun i : Fin k => w (equiv.symm (x, e) (Sum.inl i.succ))) *
              B (fun j : Fin l => w (equiv.symm (x, e) (Sum.inr j))))) =
        ∑ e : Equiv.Perm (Fin (k + l)),
          ((Equiv.Perm.sign e : ℤ) : ℂ) *
            (A (v x)
                (fun i : Fin k => (Fin.removeNth x v) (e (g (Sum.inl i)))) *
              B (fun j : Fin l => (Fin.removeNth x v) (e (g (Sum.inr j))))) := by
    classical
    refine Finset.sum_congr rfl ?_
    intro e _
    -- Use the three pointwise identities.
    simp [hL0 (e := e), hLs (e := e), hR (e := e)]

  -- Finish by combining `hsum_match` with `hrhs`.
  simpa [hsum_match] using hrhs.symm

private lemma alternatizeUncurryFin_domCoprod_alternatization_wedge_right_core {k l : ℕ}
    (v : Fin (k + l + 1) → TangentModel n)
    (A : TangentModel n →L[ℝ] Alt n k)
    (B : Alt n l) :
    (LinearMap.mul' ℝ ℂ)
        ((MultilinearMap.alternatization
            ((ContinuousAlternatingMap.alternatizeUncurryFin (𝕜 := ℝ) (F := ℂ) A).toMultilinearMap.domCoprod
              B.toMultilinearMap))
          (((v ∘ finCongr (show (k + 1) + l = (k + l) + 1 by omega)) ∘ finSumFinEquiv))) =
      (k + 1 : ℂ) *
        ∑ x : Fin (k + l + 1),
          ((-1 : ℂ) ^ (x : ℕ)) *
            (LinearMap.mul' ℝ ℂ)
              ((MultilinearMap.alternatization
                  ((A (v x)).toMultilinearMap.domCoprod B.toMultilinearMap))
                ((Fin.removeNth x v) ∘ finSumFinEquiv)) := by
  classical
  let h : (k + 1) + l = (k + l) + 1 := by omega
  let v' : Fin ((k + 1) + l) → TangentModel n := v ∘ finCongr h
  let w : (Fin (k + 1) ⊕ Fin l) → TangentModel n := v' ∘ finSumFinEquiv

  -- Expand the LHS alternatization as a permutation sum.
  have hLHS :
      (LinearMap.mul' ℝ ℂ)
          ((MultilinearMap.alternatization
              ((ContinuousAlternatingMap.alternatizeUncurryFin (𝕜 := ℝ) (F := ℂ) A).toMultilinearMap.domCoprod
                B.toMultilinearMap))
            w) =
        ∑ σ : Equiv.Perm (Fin (k + 1) ⊕ Fin l),
          ((Equiv.Perm.sign σ : ℤ) : ℂ) *
            ((ContinuousAlternatingMap.alternatizeUncurryFin (𝕜 := ℝ) (F := ℂ) A)
                (fun i : Fin (k + 1) => w (σ (Sum.inl i))) *
              B (fun j : Fin l => w (σ (Sum.inr j)))) := by
    classical
    -- First expand alternatization/domCoprod down to a signed sum in `ℂ`.
    -- (We delay converting the `ℤˣ`-action to multiplication until after applying `mul'`.)
    simp [MultilinearMap.alternatization_apply, MultilinearMap.domDomCongr_apply,
      MultilinearMap.domCoprod_apply, LinearMap.mul'_apply, Function.comp_apply]
    -- Now convert `Equiv.Perm.sign σ • z` (a `ℤˣ`-action) into multiplication by `((sign σ : ℤ) : ℂ)`.
    simp [Units.smul_def, zsmul_eq_mul]

  -- Apply stage1 (cycleRange reindexing) then stage2 (decomposeFinCycleRange reindexing).
  have hstage1 := stage1_lemma (n := n) (k := k) (l := l) (w := w) (A := A) (B := B)
  have hstage2 := stage2_lemma (n := n) (k := k) (l := l) (v := v) (A := A) (B := B)

  -- Replace the `finCongr (show ...)` in the statement by our local `h` (proof irrelevance).
  have hh : (show (k + 1) + l = (k + l) + 1 by omega) = h := by
    apply Subsingleton.elim

  -- Now finish by rewriting the LHS to the stage1 sum, then substituting stage1+stage2.
  calc
    (LinearMap.mul' ℝ ℂ)
        ((MultilinearMap.alternatization
            ((ContinuousAlternatingMap.alternatizeUncurryFin (𝕜 := ℝ) (F := ℂ) A).toMultilinearMap.domCoprod
              B.toMultilinearMap))
          (((v ∘ finCongr (show (k + 1) + l = (k + l) + 1 by omega)) ∘ finSumFinEquiv))) =
        (LinearMap.mul' ℝ ℂ)
          ((MultilinearMap.alternatization
              ((ContinuousAlternatingMap.alternatizeUncurryFin (𝕜 := ℝ) (F := ℂ) A).toMultilinearMap.domCoprod
                B.toMultilinearMap))
            w) := by
          simp [w, v', hh, h]
    _ = (k + 1 : ℂ) *
          ∑ σ : Equiv.Perm (Fin (k + 1) ⊕ Fin l),
            ((Equiv.Perm.sign σ : ℤ) : ℂ) *
              (A (w (σ (Sum.inl 0)))
                  (fun i : Fin k => w (σ (Sum.inl i.succ))) *
                B (fun j : Fin l => w (σ (Sum.inr j)))) := by
          -- Expand to the stage1 LHS, then apply `stage1_lemma`.
          -- (hLHS matches the LHS of `stage1_lemma`.)
          simpa [hLHS] using hstage1
    _ = (k + 1 : ℂ) *
          ∑ x : Fin (k + l + 1),
            ((-1 : ℂ) ^ (x : ℕ)) *
              (LinearMap.mul' ℝ ℂ)
                ((MultilinearMap.alternatization
                    ((A (v x)).toMultilinearMap.domCoprod B.toMultilinearMap))
                  ((Fin.removeNth x v) ∘ finSumFinEquiv)) := by
          -- Substitute the inner sum using `stage2_lemma`.
          -- Apply `stage2_lemma` under the scalar factor `(k+1)`.
          simpa [w, v', h] using congrArg (fun t => (k + 1 : ℂ) * t) hstage2

/-!
#### Wedge with a 0-form

`ContinuousAlternatingMap.wedgeℂ` is defined via `AlternatingMap.domCoprod`, which is a finite sum
over the quotient `Equiv.Perm.ModSumCongr`. When one side is empty (`Fin 0`) this quotient is a
singleton, and wedging with a 0-form reduces to scalar multiplication.
-/

private lemma sumCongrHom_surj_empty_left {l : ℕ} :
    Function.Surjective (Equiv.Perm.sumCongrHom (Fin 0) (Fin l)) := by
  intro σ
  have h_pres : ∀ i : Fin l, ∃ j : Fin l, σ (Sum.inr i) = Sum.inr j := by
    intro i
    rcases σ (Sum.inr i) with ⟨x⟩ | ⟨j⟩
    · exact (IsEmpty.false x).elim
    · exact ⟨j, rfl⟩
  let q_fun : Fin l → Fin l := fun i => (h_pres i).choose
  have hq : ∀ i, σ (Sum.inr i) = Sum.inr (q_fun i) := fun i => (h_pres i).choose_spec
  have q_inj : Function.Injective q_fun := by
    intro i j hij
    have : σ (Sum.inr i) = σ (Sum.inr j) := by simp [hq, hij]
    exact Sum.inr_injective (σ.injective this)
  have q_surj : Function.Surjective q_fun := by
    intro j
    obtain ⟨x, hx⟩ := σ.surjective (Sum.inr j)
    rcases x with ⟨y⟩ | ⟨i⟩
    · exact (IsEmpty.false y).elim
    · refine ⟨i, ?_⟩
      have h1 : σ (Sum.inr i) = (Sum.inr j : Fin 0 ⊕ Fin l) := hx
      have h2 : σ (Sum.inr i) = (Sum.inr (q_fun i) : Fin 0 ⊕ Fin l) := hq i
      exact Sum.inr_injective (by rw [← h2, h1])
  let q : Equiv.Perm (Fin l) := Equiv.ofBijective q_fun ⟨q_inj, q_surj⟩
  refine ⟨(1, q), ?_⟩
  ext x
  rcases x with ⟨y⟩ | ⟨i⟩
  · exact (IsEmpty.false y).elim
  · simp only [Equiv.Perm.sumCongrHom_apply, Equiv.Perm.sumCongr_apply, Sum.map_inr]
    exact (hq i).symm

private instance subsingleton_modSumCongr_empty_left {l : ℕ} :
    Subsingleton (Equiv.Perm.ModSumCongr (Fin 0) (Fin l)) := by
  constructor
  intro σ₁ σ₂
  induction σ₁ using Quotient.inductionOn' with
  | h s₁ =>
    induction σ₂ using Quotient.inductionOn' with
    | h s₂ =>
      apply Quotient.sound'
      rw [QuotientGroup.leftRel_apply]
      obtain ⟨pq, hpq⟩ := sumCongrHom_surj_empty_left (l := l) (s₁⁻¹ * s₂)
      exact ⟨pq, hpq⟩

private lemma sumCongrHom_surj_empty_right {k : ℕ} :
    Function.Surjective (Equiv.Perm.sumCongrHom (Fin k) (Fin 0)) := by
  intro σ
  have h_pres : ∀ i : Fin k, ∃ j : Fin k, σ (Sum.inl i) = Sum.inl j := by
    intro i
    rcases σ (Sum.inl i) with ⟨j⟩ | ⟨x⟩
    · exact ⟨j, rfl⟩
    · exact (IsEmpty.false x).elim
  let p_fun : Fin k → Fin k := fun i => (h_pres i).choose
  have hp : ∀ i, σ (Sum.inl i) = Sum.inl (p_fun i) := fun i => (h_pres i).choose_spec
  have p_inj : Function.Injective p_fun := by
    intro i j hij
    have : σ (Sum.inl i) = σ (Sum.inl j) := by simp [hp, hij]
    exact Sum.inl_injective (σ.injective this)
  have p_surj : Function.Surjective p_fun := by
    intro j
    obtain ⟨x, hx⟩ := σ.surjective (Sum.inl j)
    rcases x with ⟨i⟩ | ⟨y⟩
    · refine ⟨i, ?_⟩
      have h1 : σ (Sum.inl i) = (Sum.inl j : Fin k ⊕ Fin 0) := hx
      have h2 : σ (Sum.inl i) = (Sum.inl (p_fun i) : Fin k ⊕ Fin 0) := hp i
      exact Sum.inl_injective (by rw [← h2, h1])
    · exact (IsEmpty.false y).elim
  let p : Equiv.Perm (Fin k) := Equiv.ofBijective p_fun ⟨p_inj, p_surj⟩
  refine ⟨(p, 1), ?_⟩
  ext x
  rcases x with ⟨i⟩ | ⟨y⟩
  · simp only [Equiv.Perm.sumCongrHom_apply, Equiv.Perm.sumCongr_apply, Sum.map_inl]
    exact (hp i).symm
  · exact (IsEmpty.false y).elim

private instance subsingleton_modSumCongr_empty_right {k : ℕ} :
    Subsingleton (Equiv.Perm.ModSumCongr (Fin k) (Fin 0)) := by
  constructor
  intro σ₁ σ₂
  induction σ₁ using Quotient.inductionOn' with
  | h s₁ =>
    induction σ₂ using Quotient.inductionOn' with
    | h s₂ =>
      apply Quotient.sound'
      rw [QuotientGroup.leftRel_apply]
      obtain ⟨pq, hpq⟩ := sumCongrHom_surj_empty_right (k := k) (s₁⁻¹ * s₂)
      exact ⟨pq, hpq⟩

private lemma sum_subsingleton {α : Type*} [Fintype α] [Subsingleton α]
    {M : Type*} [AddCommMonoid M] (f : α → M) (a : α) : ∑ x : α, f x = f a := by
  have h : ∀ x : α, x = a := fun x => Subsingleton.elim x a
  simp only [Finset.sum_eq_single a (fun b _ hb => absurd (h b) hb)
    (fun ha => absurd (Finset.mem_univ a) ha)]

private lemma wedgeℂ_constOfIsEmpty_right {k : ℕ} (c : ℂ) (ω : Alt n k) :
    ContinuousAlternatingMap.wedgeℂ (E := TangentModel n) ω
        (ContinuousAlternatingMap.constOfIsEmpty ℝ (TangentModel n) (ι := Fin 0) c) =
      (c • ω).domDomCongr (finCongr (Nat.add_zero k).symm) := by
  classical
  ext v
  simp only [ContinuousAlternatingMap.wedgeℂ_apply, ContinuousAlternatingMap.wedgeℂ_linear]
  simp only [ContinuousAlternatingMap.domDomCongr_apply, ContinuousAlternatingMap.smul_apply]
  simp only [AlternatingMap.domDomCongr_apply, LinearMap.compAlternatingMap_apply,
    AlternatingMap.domCoprod'_apply, AlternatingMap.domCoprod_apply, MultilinearMap.sum_apply]
  let σ₀ : Equiv.Perm.ModSumCongr (Fin k) (Fin 0) := ⟦1⟧
  have hsum :
      (∑ a : Equiv.Perm.ModSumCongr (Fin k) (Fin 0),
          (AlternatingMap.domCoprod.summand ω.toAlternatingMap
              (ContinuousAlternatingMap.constOfIsEmpty ℝ (TangentModel n) (ι := Fin 0) c).toAlternatingMap a)
            (v ∘ finSumFinEquiv)) =
        (AlternatingMap.domCoprod.summand ω.toAlternatingMap
            (ContinuousAlternatingMap.constOfIsEmpty ℝ (TangentModel n) (ι := Fin 0) c).toAlternatingMap σ₀)
          (v ∘ finSumFinEquiv) :=
    sum_subsingleton (f := fun a : Equiv.Perm.ModSumCongr (Fin k) (Fin 0) =>
      (AlternatingMap.domCoprod.summand ω.toAlternatingMap
        (ContinuousAlternatingMap.constOfIsEmpty ℝ (TangentModel n) (ι := Fin 0) c).toAlternatingMap a)
        (v ∘ finSumFinEquiv)) σ₀
  rw [hsum]
  simp only [AlternatingMap.domCoprod.summand]
  conv_lhs => rw [show σ₀ = ⟦1⟧ from rfl]
  simp only [Quotient.liftOn'_mk'', MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply,
    Equiv.Perm.sign_one, one_smul, LinearMap.mul'_apply, Equiv.Perm.coe_one, id_eq, Function.comp_apply]
  have h_left :
      (fun i₁ : Fin k => v (finSumFinEquiv (m := k) (n := 0) (Sum.inl i₁))) =
        (v ∘ finCongr (Nat.add_zero k).symm) := by
    funext i
    change v (finSumFinEquiv (m := k) (n := 0) (Sum.inl i)) = v (finCongr (Nat.add_zero k).symm i)
    have hidx :
        (finSumFinEquiv (m := k) (n := 0) (Sum.inl i) : Fin (k + 0)) =
          finCongr (Nat.add_zero k).symm i := by
      have hL :
          (finSumFinEquiv (m := k) (n := 0) (Sum.inl i) : Fin (k + 0)) = Fin.castAdd 0 i := by
        simpa using (finSumFinEquiv_apply_left (m := k) (n := 0) i)
      have hR : (finCongr (Nat.add_zero k).symm i : Fin (k + 0)) = Fin.castAdd 0 i := by
        simp
      exact hL.trans hR.symm
    exact congrArg v hidx
  have h_const :
      (ContinuousAlternatingMap.constOfIsEmpty ℝ (TangentModel n) (ι := Fin 0) c).toMultilinearMap
        (fun i₂ => v (finSumFinEquiv (m := k) (n := 0) (Sum.inr i₂))) = c := rfl
  rw [h_left, h_const, smul_eq_mul, mul_comm]
  rfl

private lemma wedgeℂ_constOfIsEmpty_left {l : ℕ} (c : ℂ) (η : Alt n l) :
    ContinuousAlternatingMap.wedgeℂ (E := TangentModel n)
        (ContinuousAlternatingMap.constOfIsEmpty ℝ (TangentModel n) (ι := Fin 0) c) η =
      (c • η).domDomCongr (finCongr (Nat.zero_add l).symm) := by
  classical
  ext v
  simp only [ContinuousAlternatingMap.wedgeℂ_apply, ContinuousAlternatingMap.wedgeℂ_linear]
  simp only [ContinuousAlternatingMap.domDomCongr_apply, ContinuousAlternatingMap.smul_apply]
  simp only [AlternatingMap.domDomCongr_apply, LinearMap.compAlternatingMap_apply,
    AlternatingMap.domCoprod'_apply, AlternatingMap.domCoprod_apply, MultilinearMap.sum_apply]
  let σ₀ : Equiv.Perm.ModSumCongr (Fin 0) (Fin l) := ⟦1⟧
  have hsum :
      (∑ a : Equiv.Perm.ModSumCongr (Fin 0) (Fin l),
          (AlternatingMap.domCoprod.summand
              (ContinuousAlternatingMap.constOfIsEmpty ℝ (TangentModel n) (ι := Fin 0) c).toAlternatingMap
              η.toAlternatingMap a) (v ∘ finSumFinEquiv)) =
        (AlternatingMap.domCoprod.summand
            (ContinuousAlternatingMap.constOfIsEmpty ℝ (TangentModel n) (ι := Fin 0) c).toAlternatingMap
            η.toAlternatingMap σ₀) (v ∘ finSumFinEquiv) :=
    sum_subsingleton (f := fun a : Equiv.Perm.ModSumCongr (Fin 0) (Fin l) =>
      (AlternatingMap.domCoprod.summand
        (ContinuousAlternatingMap.constOfIsEmpty ℝ (TangentModel n) (ι := Fin 0) c).toAlternatingMap
        η.toAlternatingMap a) (v ∘ finSumFinEquiv)) σ₀
  rw [hsum]
  simp only [AlternatingMap.domCoprod.summand]
  conv_lhs => rw [show σ₀ = ⟦1⟧ from rfl]
  simp only [Quotient.liftOn'_mk'', MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply,
    Equiv.Perm.sign_one, one_smul, LinearMap.mul'_apply, Equiv.Perm.coe_one, id_eq, Function.comp_apply]
  have h_inputs :
      (fun i₂ : Fin l => v (finSumFinEquiv (m := 0) (n := l) (Sum.inr i₂))) =
        (v ∘ finCongr (Nat.zero_add l).symm) := by
    funext i
    change v (finSumFinEquiv (m := 0) (n := l) (Sum.inr i)) = v (finCongr (Nat.zero_add l).symm i)
    have hL :
        (finSumFinEquiv (m := 0) (n := l) (Sum.inr i) : Fin (0 + l)) = Fin.natAdd 0 i := by
      simpa using (finSumFinEquiv_apply_right (m := 0) (n := l) i)
    -- both sides are definitionally `i` in `Fin (0+l)`
    simpa [hL]
  rw [h_inputs]
  simp

/-! #### Base cases for shuffle bijection lemmas -/

/-- Base case for shuffle bijection right: when l = 0, B is a 0-form (scalar).
The wedge with a 0-form is just scalar multiplication, making the identity simple. -/
private lemma shuffle_bijection_right_l0 {k : ℕ}
    (v : Fin (k + 1) → TangentModel n)
    (A : TangentModel n →L[ℝ] Alt n k)
    (B : Alt n 0) :
    ∑ i : Fin (k + 1), ((-1 : ℤ)^(i : ℕ)) • ((A (v i)).wedgeℂ B) (Fin.removeNth i v) =
    ((ContinuousAlternatingMap.alternatizeUncurryFin (𝕜 := ℝ) (F := ℂ) A).wedgeℂ B)
      (v ∘ finCongr (show (k+1)+0 = k+1 by omega)) := by
  -- When l = 0, B is a 0-form (scalar), so wedge with B is scalar multiplication
  -- B = constOfIsEmpty (B 0) where 0 : Fin 0 → E is the empty function
  have hB :
      B = ContinuousAlternatingMap.constOfIsEmpty ℝ (TangentModel n) (ι := Fin 0) (B (fun _ => 0)) := by
    ext u
    simp only [ContinuousAlternatingMap.constOfIsEmpty_apply]
    congr 1
    funext i
    exact i.elim0
  -- Rewrite B as constOfIsEmpty
  rw [hB]
  -- Use `wedgeℂ_constOfIsEmpty_right`: ω.wedgeℂ (const c) = c • ω (up to `domDomCongr`)
  simp only [wedgeℂ_constOfIsEmpty_right]
  simp only [ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.domDomCongr_apply]
  -- Both sides now have the scalar B(0) factored out
  -- LHS: ∑ i, (-1)^i • (B(0) • A(v i))(removeNth i v ∘ finCongr)
  -- RHS: B(0) • (alternatizeUncurryFin A)(v ∘ finCongr ∘ finCongr)
  --
  -- Use commutativity of scalar multiplication
  conv_lhs =>
    arg 2
    ext i
    rw [smul_comm]
  rw [← Finset.smul_sum]
  congr 1
  -- Now need: ∑ i, (-1)^i • A(v i)(removeNth i v ∘ finCongr) = (alternatizeUncurryFin A)(v ∘ finCongr ∘ finCongr)
  simp only [ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  -- Simplify finCongr ∘ finCongr
  simp only [Function.comp_apply, finCongr_apply, Fin.cast_eq_self]
  -- The sums should now match after simplifying finCongr
  -- Goal: ∑ i, (-1)^i • A(v i)(removeNth i v ∘ finCongr) = ∑ j, (-1)^j • A(v j)(removeNth j v)
  -- These are equal because finCongr is the identity when k+0 = k
  rfl

/-- Shuffle Bijection Lemma (right case): alternatization commutes with wedge when
the right factor is constant. This is the identity d(ω ∧ η) = dω ∧ η for constant η.

**Mathematical Statement**: When B is a constant l-form (independent of the tangent
direction), the alternatization of the wedge equals the wedge of the alternatization.
This encodes the product rule for exterior derivatives with a constant factor.

**Proof outline**:
- LHS: ∑_i (-1)^i • (A(v_i) ∧ B)(removeNth i v)  (derivative sum outer, shuffle inner)
- RHS: ((∑_j (-1)^j • A) ∧ B)(v)  (shuffle sum outer, derivative sum via alternatize)
- Both compute the same double sum after swapping (Fubini for finite sums)

**Base case l=0**: Proved in `shuffle_bijection_right_l0` using `wedge_constOfIsEmpty_right`

**TODO**: The general case (l > 0) requires constructing the explicit bijection between:
- Pairs (i, σ) on LHS: i ∈ Fin(k+l+1), σ is a (k,l)-shuffle
- Index structure on RHS: (k+1,l)-shuffles with alternatization encoding

Reference: Bott-Tu GTM 82, Warner GTM 94 Proposition 2.14. -/
private lemma shuffle_bijection_right {k l : ℕ}
    (v : Fin ((k+l)+1) → TangentModel n)
    (A : TangentModel n →L[ℝ] Alt n k)
    (B : Alt n l) :
    ∑ i : Fin ((k+l)+1), ((-1 : ℤ)^(i : ℕ)) • ((A (v i)).wedgeℂ B) (Fin.removeNth i v) =
    ((ContinuousAlternatingMap.alternatizeUncurryFin (𝕜 := ℝ) (F := ℂ) A).wedgeℂ B)
      (v ∘ finCongr (show (k+1)+l = (k+l)+1 by omega)) := by
  -- Base case: when l = 0, B is a 0-form (scalar)
  cases l with
  | zero => exact shuffle_bijection_right_l0 v A B
  | succ l' =>
    classical
    -- General case (l = l' + 1 > 0).
    -- Rewrite the wedge terms using the full alternatization (sum over *all* permutations)
    -- to avoid working directly with the shuffle quotient `ModSumCongr`.
    have hw :
        ∀ i : Fin (k + (l' + 1) + 1),
          ((A (v i)).wedgeℂ B) (Fin.removeNth i v) =
            (((k.factorial * (l' + 1).factorial : ℕ) : ℂ)⁻¹) •
              (LinearMap.mul' ℝ ℂ)
                ((MultilinearMap.alternatization
                    (((A (v i)).toAlternatingMap.toMultilinearMap).domCoprod
                      (B.toAlternatingMap.toMultilinearMap)))
                  ((Fin.removeNth i v) ∘ finSumFinEquiv)) := by
      intro i
      simpa using
        (wedge_apply_eq_inv_factorial_smul_alternatization (n := n) (k := k) (l := l' + 1)
          (ω := A (v i)) (η := B) (v := Fin.removeNth i v))
    have hwR :
        ((ContinuousAlternatingMap.alternatizeUncurryFin (𝕜 := ℝ) (F := ℂ) A).wedgeℂ B)
            (v ∘ finCongr (show (k + 1) + (l' + 1) = (k + (l' + 1)) + 1 by omega)) =
          ((((Nat.factorial (k + 1) * (l' + 1).factorial : ℕ) : ℂ)⁻¹)) •
            (LinearMap.mul' ℝ ℂ)
              ((MultilinearMap.alternatization
                  (((ContinuousAlternatingMap.alternatizeUncurryFin (𝕜 := ℝ) (F := ℂ) A).toAlternatingMap.toMultilinearMap).domCoprod
                    (B.toAlternatingMap.toMultilinearMap)))
                (((v ∘ finCongr (show (k + 1) + (l' + 1) = (k + (l' + 1)) + 1 by omega)) ∘ finSumFinEquiv))) := by
      -- direct application of the wedge rewrite lemma
      simpa using
        (wedge_apply_eq_inv_factorial_smul_alternatization (n := n) (k := k + 1) (l := l' + 1)
          (ω := ContinuousAlternatingMap.alternatizeUncurryFin (𝕜 := ℝ) (F := ℂ) A) (η := B)
          (v := (v ∘ finCongr (show (k + 1) + (l' + 1) = (k + (l' + 1)) + 1 by omega))))
    -- Rewrite both sides.
    simp only [hw, hwR]
    -- TODO (Agent 1): finish by expanding `alternatizeUncurryFin_apply` and reindexing the
    -- resulting finite sums over permutations (Fubini + `Finset.sum_bij`).
    -- Normalize the scalar weights and clear common factors.
    -- This reduces the statement to a pure alternatization reindexing identity.
    classical
    -- First, rewrite the two factorial inverses so both sides share `(l'+1)!⁻¹ * k!⁻¹`.
    have hkfac_inv :
        (↑((k + 1).factorial) : ℂ)⁻¹ = (k + 1 : ℂ)⁻¹ * (↑(k.factorial) : ℂ)⁻¹ := by
      have hk :
          (↑((k + 1).factorial) : ℂ) = (k + 1 : ℂ) * (↑(k.factorial) : ℂ) := by
        simpa [Nat.factorial_succ, Nat.cast_mul] using
          (congrArg (fun n : ℕ => (n : ℂ)) (Nat.factorial_succ k)).symm
      calc
        (↑((k + 1).factorial) : ℂ)⁻¹ = ((k + 1 : ℂ) * (↑(k.factorial) : ℂ))⁻¹ := by simpa [hk]
        _ = (↑(k.factorial) : ℂ)⁻¹ * (k + 1 : ℂ)⁻¹ := by simp [mul_inv_rev]
        _ = (k + 1 : ℂ)⁻¹ * (↑(k.factorial) : ℂ)⁻¹ := by ac_rfl

    -- Convert the goal to a form where we can cancel the nonzero common scalar.
    have hl0 : (↑((l' + 1).factorial) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (l' + 1)
    have hk0 : (↑(k.factorial) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero k
    have hk10 : (k + 1 : ℂ) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero k
    let c : ℂ := (↑((l' + 1).factorial) : ℂ)⁻¹ * (↑(k.factorial) : ℂ)⁻¹
    have hc : c ≠ 0 := by
      refine mul_ne_zero (inv_ne_zero hl0) (inv_ne_zero hk0)
    -- Package the unscaled alternatization terms.
    let tL (x : Fin (k + (l' + 1) + 1)) : ℂ :=
      (LinearMap.mul' ℝ ℂ)
        ((MultilinearMap.alternatization
            ((A (v x)).toMultilinearMap.domCoprod B.toMultilinearMap))
          ((Fin.removeNth x v) ∘ finSumFinEquiv))
    let tR : ℂ :=
      (LinearMap.mul' ℝ ℂ)
        ((MultilinearMap.alternatization
            ((ContinuousAlternatingMap.alternatizeUncurryFin (𝕜 := ℝ) (F := ℂ) A).toMultilinearMap.domCoprod
              B.toMultilinearMap))
          (((v ∘ finCongr (show (k + 1) + (l' + 1) = (k + (l' + 1)) + 1 by omega)) ∘ finSumFinEquiv)))

    -- Rewrite both factorial scalars into the common factor `c`.
    have hcL :
        ((↑(k.factorial * (l' + 1).factorial) : ℂ)⁻¹) = c := by
      simp [c, Nat.cast_mul, mul_inv_rev]
    have hcR :
        ((↑((k + 1).factorial * (l' + 1).factorial) : ℂ)⁻¹) = (k + 1 : ℂ)⁻¹ * c := by
      -- use `hkfac_inv` for `(k+1)!` and commutativity
      simp [c, hkfac_inv, Nat.cast_mul, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm]

    -- Fold the large alternatization expressions into `tL`/`tR` without unfolding them.
    have htL' :
        ∀ x : Fin (k + (l' + 1) + 1),
          (LinearMap.mul' ℝ ℂ)
              ((MultilinearMap.alternatization
                  ((A (v x)).toMultilinearMap.domCoprod B.toMultilinearMap))
                ((Fin.removeNth x v) ∘ finSumFinEquiv)) =
            tL x := by
      intro x; rfl
    have htR' :
        (LinearMap.mul' ℝ ℂ)
            ((MultilinearMap.alternatization
                ((ContinuousAlternatingMap.alternatizeUncurryFin (𝕜 := ℝ) (F := ℂ) A).toMultilinearMap.domCoprod
                  B.toMultilinearMap))
              (((v ∘ finCongr (show (k + 1) + (l' + 1) = (k + (l' + 1)) + 1 by omega)) ∘ finSumFinEquiv))) =
          tR := by
      rfl

    -- Rewrite the goal using the folded expressions and the common scalar `c`.
    -- We keep `simp` tightly controlled to avoid unfolding the alternatization sums.
    -- First, fold the big terms and rewrite the factorial scalars via `hcL`/`hcR`.
    -- Then convert the remaining `•`-actions in `ℂ` into multiplication.
    simp only [htL', htR']
    -- Rewrite the factorial inverse scalars.
    -- (They appear inside the rewritten wedge formulas from `hw`/`hwR`.)
    simp only [hcL, hcR]
    -- Finally, normalize `ℂ` scalar actions.
    simp [smul_smul, mul_assoc, mul_left_comm, mul_comm]

    -- Factor out the common scalar `c` from both sides, cancel it, and clear `(k+1)⁻¹`.
    have hL :
        (∑ x : Fin (k + (l' + 1) + 1), (-1) ^ (x : ℕ) * (c * tL x)) =
          c * (∑ x : Fin (k + (l' + 1) + 1), (-1) ^ (x : ℕ) * tL x) := by
      -- expand the RHS using `Finset.mul_sum` and rearrange each term
      classical
      simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
        using (Finset.mul_sum (s := (Finset.univ : Finset (Fin (k + (l' + 1) + 1))))
          (f := fun x => (-1) ^ (x : ℕ) * tL x) c).symm

    have hR :
        (k + 1 : ℂ)⁻¹ * (c * tR) = c * ((k + 1 : ℂ)⁻¹ * tR) := by
      -- commutativity in `ℂ`
      ac_rfl

    -- Use `hL`/`hR` to rewrite the goal as `c * Σ = c * ((k+1)⁻¹ * tR)`.
    -- Then it suffices to prove `Σ = (k+1)⁻¹ * tR`, which follows from the core lemma.
    -- (The rewrite may be blocked if simp normalized exponents differently, so we do it by `simp`.)
    -- Rewrite both sides in place.
    -- LHS
    -- (Turn `(-1 : ℂ)^(x:ℕ)` into `(-1 : ℂ)^(x:ℤ)` if necessary, then apply `hL`.)
    -- RHS similarly.
    -- We use `rw` and `simp` to match the patterns exactly.
    -- First, rewrite to the exact `hL`/`hR` patterns.
    -- (No-op if already in that form.)
    -- Now apply the rewrites.
    rw [hL, hR]

    -- Core lemma gives `tR = (k+1) * Σ` (with the Nat-exponent form).
    have hreindexNat :
        tR =
          (k + 1 : ℂ) *
            ∑ x : Fin (k + (l' + 1) + 1), ((-1 : ℂ) ^ (x : ℕ)) * tL x := by
      simpa [tL, tR] using
        (alternatizeUncurryFin_domCoprod_alternatization_wedge_right_core (n := n)
          (k := k) (l := l' + 1) (v := v) (A := A) (B := B))

    have hsum :
        (∑ x : Fin (k + (l' + 1) + 1), (-1) ^ (x : ℕ) * tL x) = (k + 1 : ℂ)⁻¹ * tR := by
      -- Divide by `(k+1)` using the core lemma.
      have hsumNat :
          (k + 1 : ℂ)⁻¹ * tR =
            ∑ x : Fin (k + (l' + 1) + 1), ((-1 : ℂ) ^ (x : ℕ)) * tL x := by
        -- multiply `hreindexNat` by `(k+1)⁻¹` on the left
        have := congrArg (fun z : ℂ => (k + 1 : ℂ)⁻¹ * z) hreindexNat
        -- simplify
        simpa [mul_assoc, hk10, inv_mul_cancel₀ hk10] using this
      -- `hsumNat` is exactly the desired statement, up to symmetry.
      simpa using hsumNat.symm

    -- Multiply `hsum` by `c` to match the rewritten goal.
    simpa [mul_assoc, mul_left_comm, mul_comm] using congrArg (fun z : ℂ => c * z) hsum

/-- Main theorem: alternatization commutes with wedge when right factor is constant. -/
theorem alternatizeUncurryFin_wedge_right {k l : ℕ}
    (A : TangentModel n →L[ℝ] Alt n k) (B : Alt n l) :
    let wedge_right : TangentModel n →L[ℝ] Alt n (k + l) :=
      (ContinuousAlternatingMap.wedgeℂCLM_alt (E := TangentModel n) k l).flip B ∘L A
    ContinuousAlternatingMap.alternatizeUncurryFin (𝕜 := ℝ) (F := ℂ) wedge_right =
    ContinuousAlternatingMap.domDomCongr
      ((ContinuousAlternatingMap.alternatizeUncurryFin (𝕜 := ℝ) (F := ℂ) A).wedgeℂ B)
      (finCongr (show (k+1)+l = (k+l)+1 by omega)) := by
  intro wedge_right
  ext v
  simp only [ContinuousAlternatingMap.alternatizeUncurryFin_apply,
             ContinuousAlternatingMap.domDomCongr_apply]
  -- Use the shuffle bijection lemma
  have h_wedge_right : ∀ w, wedge_right w = (A w).wedgeℂ B := fun _ => rfl
  simp only [h_wedge_right]
  exact shuffle_bijection_right v A B


/-- Shuffle Bijection Lemma (left case): alternatization commutes with wedge when
the left factor is constant, with sign (-1)^k. This is d(ω ∧ η) = (-1)^k ω ∧ dη for constant ω.

**Mathematical Statement**: The sign (-1)^k accounts for moving the derivative index past
the k indices of the constant k-form A. This is the standard sign in graded commutativity.

**Index structure**:
- LHS: ∑_{i : Fin(k+l+1)} ∑_{σ : Shuffles(k,l)} (-1)^i × sign(σ) × (...)
- RHS: (-1)^k × ∑_{τ : Shuffles(k,l+1)} ∑_{j : Fin(l+1)} sign(τ) × (-1)^j × (...)

**Bijection**: (i, σ) ↔ (τ, j) with sign matching:
  (-1)^i × sign(σ) = (-1)^k × sign(τ) × (-1)^j

**Reference**: Bott-Tu GTM 82, Warner GTM 94 Proposition 2.14. -/
private lemma shuffle_bijection_left {k l : ℕ}
    (v : Fin ((k+l)+1) → TangentModel n)
    (A : Alt n k)
    (B : TangentModel n →L[ℝ] Alt n l) :
    ∑ i : Fin ((k+l)+1), ((-1 : ℤ)^(i : ℕ)) • (A.wedgeℂ (B (v i))) (Fin.removeNth i v) =
    ((-1 : ℂ)^k • A.wedgeℂ (ContinuousAlternatingMap.alternatizeUncurryFin (𝕜 := ℝ) (F := ℂ) B))
      (v ∘ finCongr (show k+(l+1) = (k+l)+1 by omega)) := by
  /-
  **Proof Strategy** (Bott-Tu GTM 82, Warner GTM 94 Proposition 2.14):

  The graded Leibniz rule for d(A ∧ B) where A is a constant k-form gives:
    d(A ∧ B) = (-1)^k A ∧ dB

  At the level of alternating maps on tangent vectors, this becomes a shuffle bijection.
  We prove this using `shuffle_bijection_right` and graded commutativity.

  **Key insight**: Using graded commutativity of wedge products (wedge_comm_domDomCongr):
    A.wedge (B v_i) = (-1)^(kl) • domDomCongr ((B v_i).wedge A) blockSwapEquiv

  Then we apply shuffle_bijection_right to the swapped form and track the resulting signs.
  -/
  classical
  -- Base case: k = 0 gives (-1)^0 = 1, trivial
  cases k with
  | zero =>
    -- When k = 0, A is a 0-form (scalar), the sign (-1)^0 = 1.
    simp only [pow_zero, one_smul]
    -- A = constOfIsEmpty (A 0)
    have hA :
        A =
          ContinuousAlternatingMap.constOfIsEmpty ℝ (TangentModel n) (ι := Fin 0) (A (fun _ => 0)) := by
      ext u
      simp only [ContinuousAlternatingMap.constOfIsEmpty_apply]
      congr 1
      funext i
      exact i.elim0
    -- Rewrite both LHS and RHS using wedge_constOfIsEmpty_left
    rw [hA]
    simp only [wedgeℂ_constOfIsEmpty_left]
    simp only [ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.domDomCongr_apply]
    -- Factor out the scalar on LHS
    conv_lhs =>
      arg 2
      ext i
      rw [smul_comm]
    rw [← Finset.smul_sum]
    congr 1
    -- Now need: ∑ i : Fin (0+l+1), (-1)^i • B(v i)(finCongr(removeNth i v)) =
    --           (alternatizeUncurryFin B)(finCongr(finCongr(v)))
    simp only [ContinuousAlternatingMap.alternatizeUncurryFin_apply]
    -- Reindex sum using finCongr equivalence
    have h_eq : (0 : ℕ) + l + 1 = l + 1 := by omega
    refine Fintype.sum_equiv (finCongr h_eq) _ _ ?_
    intro i
    -- The summands match after finCongr reindexing.
    -- All Fin.cast operations preserve .val, so both sides compute the same ℂ value.
    simp only [finCongr_apply, Fin.val_cast, Function.comp_apply]

    -- Goal: (-1)^i.val • B(v i)(removeNth i v ∘ cast) =
    --       (-1)^i.val • B(v (cast (cast (cast i))))(removeNth (cast i) (v ∘ cast ∘ cast))
    -- All Fin.cast preserve .val, so indices match, and v values match.

    -- Use `Fin.heq_ext_iff` indirectly via congrArg
    -- The key: for any a, b : Fin n, if a.val = b.val then a = b (Fin.ext)
    -- All casts preserve .val, so:
    -- 1. i.val = (cast (cast (cast i))).val
    -- 2. (succAbove i (cast j)).val = (cast (cast (succAbove (cast i) j))).val

    -- The power of -1 is equal on both sides (same i.val), so we just need to prove the B terms are equal

    -- Helper: v preserves equality when indices have same .val
    have hv : ∀ a b : Fin (0 + l + 1), a.val = b.val → v a = v b := by
      intros a b h; congr 1; exact Fin.ext h

    -- Helper: succAbove preserves .val relationship
    have hsuccAbove : ∀ (a : Fin (0 + l + 1)) (b : Fin (l + 1)) (ja : Fin (0 + l)) (jb : Fin l),
        a.val = b.val → ja.val = jb.val →
        (Fin.succAbove a ja).val = (Fin.succAbove b jb).val := by
      intros a b ja jb ha hj
      -- succAbove compares castSucc with the pivot and uses castSucc or succ
      simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
      -- The condition is: castSucc ja < a iff castSucc jb < b (since ja.val = jb.val and a.val = b.val)
      split_ifs with h1 h2
      all_goals simp only [Fin.val_castSucc, Fin.val_succ] at *
      all_goals omega

    -- Main proof: smul of equal ℂ values
    -- Goal: (-1)^i • B(v i)(f) = (-1)^i • B(v (casts i))(g)
    -- Both sides evaluate to the same ℂ because all Fin.cast/finCongr preserve .val.
    --
    -- Mathematical argument:
    -- 1. The power (-1)^i is equal since i.val = (finCongr h_eq i).val (casts preserve .val)
    -- 2. B(v i) = B(v (casts i)) since v i = v (casts i) (again, casts preserve .val)
    -- 3. The removeNth functions are pointwise equal since succAbove depends only on .val
    --    (proven by hsuccAbove above)
    --
    -- Lean-level issue:
    -- The finCongr expressions in the goal use inferred equality proofs that don't match
    -- the proofs we can construct (e.g., goal has `l + 1 = l + 1` but we provide `l + 1 = 0 + (l + 1)`).
    -- This is a propositional vs definitional equality issue - both proofs are valid but
    -- Lean's type system doesn't see them as equal without explicit proof transport.
    --
    -- The equality holds by the fact that all operations (Fin.cast, finCongr, succAbove)
    -- preserve the underlying .val, so the ℂ computation is identical.

    -- Goal: (-1)^i • B(v i)(f) = (-1)^i • B(v (casts i))(g)
    -- Both sides evaluate to the same ℂ because all Fin.cast/finCongr preserve .val.
    --
    -- Mathematical justification:
    -- 1. The power (-1)^i is equal since i.val = (finCongr h_eq i).val
    -- 2. B(v i) = B(v (casts i)) since v i = v (casts i) (casts preserve .val)
    -- 3. The removeNth functions are pointwise equal since succAbove depends only on .val
    --
    -- Lean-level complexity:
    -- The finCongr expressions in the goal use inferred equality proofs that differ
    -- from what we can construct. This is purely a type-level issue - the ℂ computations
    -- are provably identical.
    --
    -- The hsuccAbove lemma above establishes the key index equality.
    -- The hv lemma establishes that v values are equal when indices have equal .val.

    -- Direct proof using congr: split into B argument and function argument
    -- The congr 1 splits the smul, then congr 1 splits B(v i)(f) = B(v (casts i))(g)
    congr 1
    congr 1
    -- Goal 1: v i = v (casts i) - indices have equal .val
    -- Goal 2: f = g - function equality via pointwise hv and hsuccAbove
    all_goals first
      | apply hv; simp only [Fin.val_cast]
      | (funext j; simp only [Function.comp_apply, Fin.removeNth, finCongr_apply];
         apply hv; simp only [Fin.val_cast]; apply hsuccAbove <;> simp only [Fin.val_cast])
  | succ k' =>
    classical
    -- Step 1: swap the wedge factors inside each summand.
    have hswap :
        ∀ i : Fin ((k' + 1) + l + 1),
          (A.wedgeℂ (B (v i))) (Fin.removeNth i v) =
            (B (v i)).wedgeℂ A ((Fin.removeNth i v) ∘ (blockSwapEquiv (k' + 1) l).symm) := by
      intro i
      simpa [ContinuousAlternatingMap.domDomCongr_apply, Function.comp_apply] using
        congrArg (fun f => f (Fin.removeNth i v))
          (wedge_comm_domDomCongr (A := A) (B := B (v i)))
    conv_lhs =>
      arg 2
      ext i
      rw [hswap i]

    -- Step 2: remove the explicit `blockSwapEquiv` from the argument using alternatingness,
    -- picking up the sign of the block-swap permutation, i.e. `(-1)^((k'+1)*l)`.
    have hswapArg :
        ∀ i : Fin ((k' + 1) + l + 1),
          ((B (v i)).wedgeℂ A) ((Fin.removeNth i v) ∘ (blockSwapEquiv (k' + 1) l).symm) =
            (Equiv.Perm.sign (blockSwapPerm (k' + 1) l)) •
              ((B (v i)).wedgeℂ A)
                ((Fin.removeNth i v) ∘ finCongr (Nat.add_comm l (k' + 1))) := by
      intro i
      let e : Fin ((k' + 1) + l) ≃ Fin (l + (k' + 1)) := finCongr (Nat.add_comm (k' + 1) l)
      let σ : Equiv.Perm (Fin (l + (k' + 1))) :=
        e.permCongr (blockSwapPerm (k' + 1) l).symm
      let w0 : Fin (l + (k' + 1)) → TangentModel n :=
        (Fin.removeNth i v) ∘ finCongr (Nat.add_comm l (k' + 1))
      have hw :
          (Fin.removeNth i v) ∘ (blockSwapEquiv (k' + 1) l).symm = w0 ∘ σ := by
        funext x
        -- `σ` is the conjugate of `(blockSwapPerm (k'+1) l)⁻¹` by the cast `e`,
        -- and `(blockSwapEquiv (k'+1) l).symm` is the corresponding casted map.
        simp [σ, e, w0, blockSwapPerm, Function.comp_apply, Equiv.permCongr_apply]
      have hmap :
          ((B (v i)).wedgeℂ A) (w0 ∘ σ) = (Equiv.Perm.sign σ) • ((B (v i)).wedgeℂ A) w0 := by
        simpa [w0, σ] using (((B (v i)).wedgeℂ A).toAlternatingMap.map_perm w0 σ)
      have hsign :
          Equiv.Perm.sign σ = Equiv.Perm.sign (blockSwapPerm (k' + 1) l) := by
        have :
            Equiv.Perm.sign σ =
              Equiv.Perm.sign ((blockSwapPerm (k' + 1) l).symm) := by
          simpa [σ] using
            (Equiv.Perm.sign_permCongr e ((blockSwapPerm (k' + 1) l).symm))
        simpa using this.trans (by simpa using (Equiv.Perm.sign_inv (blockSwapPerm (k' + 1) l)))
      calc
        ((B (v i)).wedgeℂ A) ((Fin.removeNth i v) ∘ (blockSwapEquiv (k' + 1) l).symm)
            = ((B (v i)).wedgeℂ A) (w0 ∘ σ) := by simpa [hw]
        _ = (Equiv.Perm.sign σ) • ((B (v i)).wedgeℂ A) w0 := hmap
        _ = (Equiv.Perm.sign (blockSwapPerm (k' + 1) l)) • ((B (v i)).wedgeℂ A) w0 := by
              simpa [hsign]
        _ = (Equiv.Perm.sign (blockSwapPerm (k' + 1) l)) •
              ((B (v i)).wedgeℂ A)
                ((Fin.removeNth i v) ∘ finCongr (Nat.add_comm l (k' + 1))) := rfl

    conv_lhs =>
      arg 2
      ext i
      rw [hswapArg i]

    -- Pull the constant sign factor out of the sum.
    have hsign_out :
        (∑ i : Fin ((k' + 1) + l + 1),
            ((-1 : ℤ) ^ (i : ℕ)) •
              ((Equiv.Perm.sign (blockSwapPerm (k' + 1) l)) •
                ((B (v i)).wedgeℂ A)
                  ((Fin.removeNth i v) ∘ finCongr (Nat.add_comm l (k' + 1))))) =
          (Equiv.Perm.sign (blockSwapPerm (k' + 1) l)) •
            (∑ i : Fin ((k' + 1) + l + 1),
              ((-1 : ℤ) ^ (i : ℕ)) •
                ((B (v i)).wedgeℂ A)
                  ((Fin.removeNth i v) ∘ finCongr (Nat.add_comm l (k' + 1)))) := by
      classical
      -- Convert the `ℤˣ`-action to a `ℤ`-action to commute with `(-1)^i`, then factor out.
      -- This is safe since `Equiv.Perm.sign σ : ℤˣ` is always `±1`.
      let u : ℤˣ := Equiv.Perm.sign (blockSwapPerm (k' + 1) l)
      -- rewrite `u • x` as `(↑u : ℤ) • x`
      simp [u, Units.smul_def, Finset.smul_sum, smul_smul, mul_assoc, mul_left_comm, mul_comm]

    -- Reindex the inner sum to match `shuffle_bijection_right` for `(B, A)`.
    have hdim1 : (k' + 1) + l + 1 = l + (k' + 1) + 1 := by omega
    let v' : Fin (l + (k' + 1) + 1) → TangentModel n := v ∘ finCongr hdim1.symm
    have hreindex :
        (∑ i : Fin ((k' + 1) + l + 1),
            ((-1 : ℤ) ^ (i : ℕ)) •
              ((B (v i)).wedgeℂ A)
                ((Fin.removeNth i v) ∘ finCongr (Nat.add_comm l (k' + 1)))) =
          ∑ j : Fin (l + (k' + 1) + 1),
            ((-1 : ℤ) ^ (j : ℕ)) •
              ((B (v' j)).wedgeℂ A) (Fin.removeNth j v') := by
      classical
      -- Reindex by the value-preserving cast `finCongr hdim1`.
      refine Fintype.sum_equiv (finCongr hdim1)
        (fun i : Fin ((k' + 1) + l + 1) =>
          ((-1 : ℤ) ^ (i : ℕ)) •
            ((B (v i)).wedgeℂ A)
              ((Fin.removeNth i v) ∘ finCongr (Nat.add_comm l (k' + 1))))
        (fun j : Fin (l + (k' + 1) + 1) =>
          ((-1 : ℤ) ^ (j : ℕ)) •
            ((B (v' j)).wedgeℂ A) (Fin.removeNth j v'))
        ?_
      intro i
      -- The `finCongr` reindexing preserves `.val`, hence preserves the `(-1)^i` factor.
      -- It also satisfies `v' (finCongr hdim1 i) = v i`.
      set j : Fin (l + (k' + 1) + 1) := (finCongr hdim1) i
      have hjval : (j : ℕ) = (i : ℕ) := by
        -- `finCongr` is a cast, hence preserves `.val`.
        simp [j, finCongr_apply, Fin.val_cast]
      -- Reduce the goal to an equality of the wedge evaluation arguments.
      -- After rewriting, both sides are multiplied by the same `(-1)^i`.
      have hvj : v' j = v i := by
        -- `v' = v ∘ (finCongr hdim1.symm)` and `finCongr` is an equivalence.
        simp [v', j, Function.comp_apply]
      -- Rewrite the RHS summand using `hjval` and `hvj`.
      -- Now it suffices to show the argument functions of the wedge agree.
      have harg :
          (Fin.removeNth i v) ∘ finCongr (Nat.add_comm l (k' + 1)) = Fin.removeNth j v' := by
        funext x
        -- Unfold `removeNth` via `succAbove`.
        simp only [Fin.removeNth_apply, Function.comp_apply]
        -- Expand `v'`.
        simp only [v', Function.comp_apply]
        -- Reduce to a statement about the indices given to `v`.
        -- It suffices to show the indices are equal (they have the same `.val`).
        apply congrArg v
        apply Fin.ext
        -- Compute both sides using a value formula for `succAbove`.
        have hval_succAbove {m : ℕ} (p : Fin (m + 1)) (y : Fin m) :
            (p.succAbove y).val = if y.val < p.val then y.val else y.val + 1 := by
          by_cases h : y.val < p.val
          · have hcast : y.castSucc < p := by
              -- `castSucc` preserves `.val`.
              simpa [Fin.lt_def, Fin.val_castSucc] using h
            simp [Fin.succAbove, Fin.lt_def, h, hcast, Fin.val_castSucc, Fin.val_succ]
          · have hcast : ¬ y.castSucc < p := by
              intro h'
              exact h (by simpa [Fin.lt_def, Fin.val_castSucc] using h')
            have hle : p.val ≤ y.val := le_of_not_gt h
            simp [Fin.succAbove, Fin.lt_def, h, hcast, hle, Fin.val_castSucc, Fin.val_succ]
        -- Now both sides reduce to the same `if`-expression.
        simp [j, hjval, finCongr_apply, Fin.val_cast, hval_succAbove]
      -- Finish by rewriting everything.
      -- (`hjval` handles the `(-1)^` factor; `hvj` handles the `B` argument.)
      -- After rewriting, both sides are identical.
      have hvj' : v' (Fin.cast hdim1 i) = v i := by
        simpa [j, finCongr_apply] using hvj
      simp [j, hjval, hvj', harg]

    -- Apply the right-case shuffle bijection to `(B, A)`.
    have hsbr := shuffle_bijection_right v' B A

    -- Combine everything.
    -- First rewrite the LHS into the `v'`-indexed form, then use `hsbr`.
    -- Finally, rewrite the RHS back to the target statement using graded sign arithmetic.
    have hsign_block :
        Equiv.Perm.sign (blockSwapPerm (k' + 1) l) = (-1 : ℤˣ) ^ ((k' + 1) * l) :=
      sign_blockSwapPerm (k := k' + 1) (l := l)
    -- Rewrite using `hsign_out`, `hreindex`, and `hsbr`.
    -- The remaining goal is exactly the graded Leibniz sign identity.
    -- (We convert the `ℤˣ`-action to `ℂ` multiplication and use `wedge_comm_domDomCongr`
    --  once more to swap back.)
    --
    -- Start from the factored-and-reindexed form.
    -- LHS
    rw [hsign_out, hreindex, hsbr]
    -- Convert `ℤˣ`-actions to multiplication in `ℂ`.
    -- This turns `Equiv.Perm.sign ... • z` into multiplication by `(-1)^(...)`.
    have hsignC :
        ((Equiv.Perm.sign (blockSwapPerm (k' + 1) l) : ℤˣ) : ℂ) = (-1 : ℂ) ^ ((k' + 1) * l) := by
      -- use `hsign_block` then coerce `ℤˣ` → `ℤ` → `ℂ`
      -- (`(-1 : ℤˣ)` coerces to `(-1 : ℂ)`).
      simpa [hsign_block]
    -- Rewrite the `ℤˣ`-smul on `ℂ` as multiplication.
    simp [Units.smul_def, zsmul_eq_mul, hsignC, mul_assoc, mul_left_comm, mul_comm]
    -- Now both sides are scalar multiples of wedge evaluations. We finish by graded commutativity:
    -- `A ∧ altB = domDomCongr (altB ∧ A) (blockSwapEquiv (k'+1) (l+1)).symm`,
    -- and the resulting permutation has sign `(-1)^((k'+1)*(l+1))`.
    --
    -- Set `altB := alternatizeUncurryFin B` to shorten notation.
    set altB : Alt n (l + 1) := ContinuousAlternatingMap.alternatizeUncurryFin (F := ℂ) B

    -- Convert the remaining goal to one about `wedgeℂ`, so that we can use `wedge_comm_domDomCongr`.
    let w₁ : Fin ((l + 1) + (k' + 1)) → TangentModel n :=
      v' ∘ (finCongr (show (l + 1) + (k' + 1) = l + (k' + 1) + 1 by omega))
    -- Replace the `wedgeℂ_linear` evaluations by `wedgeℂ` evaluations.
    rw [← (ContinuousAlternatingMap.wedgeℂ_apply (ω := altB) (η := A) (v := w₁))]
    rw [← (ContinuousAlternatingMap.wedgeℂ_apply (ω := A) (η := altB))]

    -- Rewrite the RHS wedge using `wedge_comm_domDomCongr`.
    have hcomm' : A.wedgeℂ altB =
        ContinuousAlternatingMap.domDomCongr (altB.wedgeℂ A) (blockSwapEquiv (k' + 1) (l + 1)).symm :=
      wedge_comm_domDomCongr (A := A) (B := altB)
    rw [hcomm']
    -- Evaluate the `domDomCongr`.
    simp [ContinuousAlternatingMap.domDomCongr_apply, altB, Function.comp_apply]

    -- Now both sides are evaluations of `(altB ∧ A)` at two vectors related by a permutation.
    -- Use alternatingness to extract the sign of the block swap of sizes `(l+1)` and `(k'+1)`.
    let σ : Equiv.Perm (Fin ((l + 1) + (k' + 1))) :=
      (blockSwapPerm (l + 1) (k' + 1))
    have hσsign : (Equiv.Perm.sign σ : ℂ) = (-1 : ℂ) ^ ((l + 1) * (k' + 1)) := by
      -- `sign_blockSwapPerm` works for any `k l`.
      simpa [σ, sign_blockSwapPerm (k := l + 1) (l := k' + 1)]

    -- Relate the two argument vectors by `σ` (a cyclic rotation).
    have hw :
        (v ∘ ⇑((blockSwapEquiv (k' + 1) (l + 1)).symm)) =
          (v' ∘ ⇑(finCongr (show (l + 1) + (k' + 1) = l + (k' + 1) + 1 by omega))) ∘ σ := by
      funext x
      have hbs :
          (blockSwapEquiv (k' + 1) (l + 1)).symm = blockSwapEquiv (l + 1) (k' + 1) := by
        ext y <;> simp [blockSwapEquiv]
      -- all casts preserve `.val`; the only nontrivial part is the block swap.
      -- We discharge this by unfolding `σ`/`blockSwapPerm` and simplifying.
      simp [σ, blockSwapPerm, Function.comp_apply, Equiv.permCongr_apply, finCongr_apply, v', hdim1,
        hbs]

    -- Apply `map_perm` for the alternating map `(altB ∧ A).toAlternatingMap`, but in the direction
    -- that yields `g w₁ = sign σ • g w₂`.
    have hw' :
        (v' ∘ ⇑(finCongr (show (l + 1) + (k' + 1) = l + (k' + 1) + 1 by omega))) =
          (v ∘ ⇑((blockSwapEquiv (k' + 1) (l + 1)).symm)) ∘ σ.symm := by
      funext x
      -- Evaluate `hw` at `σ.symm x` and simplify.
      have hx := congrArg (fun f => f (σ.symm x)) hw
      simpa [Function.comp_apply] using hx.symm
    have hperm :
        (altB.wedgeℂ A) (v' ∘ ⇑(finCongr (show (l + 1) + (k' + 1) = l + (k' + 1) + 1 by omega))) =
          (Equiv.Perm.sign σ : ℤˣ) •
            (altB.wedgeℂ A) (v ∘ ⇑((blockSwapEquiv (k' + 1) (l + 1)).symm)) := by
      -- Start from `map_perm` with `σ.symm`.
      have hmap :=
        ((altB.wedgeℂ A).toAlternatingMap.map_perm
          (v ∘ ⇑((blockSwapEquiv (k' + 1) (l + 1)).symm))
          (σ.symm))
      -- `map_perm` gives `g (w₂ ∘ σ⁻¹) = sign σ⁻¹ • g w₂`.
      -- Rewrite `w₂ ∘ σ⁻¹` as `w₁` using `hw'`, and rewrite `sign σ⁻¹ = sign σ`.
      have hsignInv : Equiv.Perm.sign (σ.symm) = Equiv.Perm.sign σ := by
        simpa using (Equiv.Perm.sign_inv σ)
      -- Finish.
      simpa [hw', hsignInv, Function.comp_apply] using hmap

    -- Substitute `hperm` and use the explicit sign value `hσsign`.
    -- This is exactly the parity computation:
    -- `(-1)^(l*(k'+1)) * (-1)^((l+1)*(k'+1)) = (-1)^(k'+1)`.
    -- Note: `Equiv.Perm.sign σ : ℤˣ` acts on `ℂ` by multiplication by its coercion.
    -- We convert the unit action and close by `simp`/`omega`.
    have hpar :
        (-1 : ℂ) ^ ((k' + 1) * l) * (-1 : ℂ) ^ ((l + 1) * (k' + 1)) = (-1 : ℂ) ^ (k' + 1) := by
      -- same parity argument as in the comments above.
      calc
        (-1 : ℂ) ^ ((k' + 1) * l) * (-1 : ℂ) ^ ((l + 1) * (k' + 1))
            = (-1 : ℂ) ^ (((k' + 1) * l) + ((l + 1) * (k' + 1))) := by
                simp [pow_add]
        _ = (-1 : ℂ) ^ (((k' + 1) * l) + ((k' + 1) * (l + 1))) := by
                simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        _ = (-1 : ℂ) ^ ((k' + 1) * (l + (l + 1))) := by
                simp [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]
        _ = (-1 : ℂ) ^ ((k' + 1) * (2 * l + 1)) := by
              -- reduce to equality of exponents
              have hl : l + (l + 1) = 2 * l + 1 := by
                calc
                  l + (l + 1) = (l + l) + 1 := by
                    simpa using (Nat.add_assoc l l 1).symm
                  _ = 2 * l + 1 := by
                    simp [two_mul, Nat.add_assoc]
              simp [hl]
        _ = (-1 : ℂ) ^ (k' + 1) := by
              -- `(-1)^(m*(2*l+1)) = (-1)^m` since `2*l` is even.
              have hm : (k' + 1) * (2 * l + 1) = (k' + 1) + (k' + 1) * (2 * l) := by
                calc
                  (k' + 1) * (2 * l + 1) = (k' + 1) * (2 * l) + (k' + 1) * 1 := by
                    simpa [Nat.mul_add]
                  _ = (k' + 1) * (2 * l) + (k' + 1) := by simp
                  _ = (k' + 1) + (k' + 1) * (2 * l) := by
                    simpa using (Nat.add_comm ((k' + 1) * (2 * l)) (k' + 1))
              rw [hm, pow_add]
              have hkill : (-1 : ℂ) ^ ((k' + 1) * (2 * l)) = 1 := by
                -- make the even factor `2*l` the left factor, so `pow_mul` reduces to `(-1)^(2*l)=1`
                rw [Nat.mul_comm (k' + 1) (2 * l)]
                rw [pow_mul]
                have h2 : (-1 : ℂ) ^ (2 * l) = 1 := by
                  -- `(-1)^(2*l) = ((-1)^2)^l = 1`
                  rw [pow_mul]
                  simp
                simp [h2]
              simp [hkill]
    -- Final step: rewrite using `hperm`, `hσsign`, and `hpar`.
    -- (This also folds back the various `pow_mul` normalizations introduced by simp.)
    -- First convert the `ℤˣ`-smul to multiplication in `ℂ`.
    -- Then use `hσsign` to identify the unit as a `(-1)^...` power, and apply `hpar`.
    -- Note: we also use `altB` to rewrite `alternatizeUncurryFin B`.
    -- `simp` is enough after these rewrites.
    -- (We keep the simp-set small to avoid looping.)
    -- Start by rewriting with `hperm`.
    -- LHS has `g w₁`, RHS has `g w₂`.
    -- Replace `g w₁` using `hperm`, then simplify scalar factors.
    -- (All remaining work is commutative ring arithmetic in `ℂ`.)
    --
    -- Convert `wedgeℂ_linear` evaluations to `wedgeℂ`.
    rw [← (ContinuousAlternatingMap.wedgeℂ_apply (ω := altB) (η := A) (v := w₁))]
    -- Unfold `altB` on the LHS so both sides use `alternatizeUncurryFin B`,
    -- without rewriting `wedge` back into `wedgeAlternating`.
    dsimp [altB]
    -- Let `w₂` be the RHS argument vector without the redundant `Equiv.refl`.
    let w₂ : Fin ((l + 1) + (k' + 1)) → TangentModel n :=
      v ∘ ⇑(blockSwapEquiv (k' + 1) (l + 1)).symm
    have hw2 :
        (v ∘ ⇑(Equiv.refl (Fin (k' + 1 + (l + 1))))) ∘
            ⇑(blockSwapEquiv (k' + 1) (l + 1)).symm =
          w₂ := by
      funext x
      simp [w₂, Function.comp_apply]
    have hw2_val :
        ((ContinuousAlternatingMap.alternatizeUncurryFin (𝕜 := ℝ) (F := ℂ) B).wedgeℂ A)
            ((v ∘ ⇑(Equiv.refl (Fin (k' + 1 + (l + 1))))) ∘
              ⇑(blockSwapEquiv (k' + 1) (l + 1)).symm) =
          ((ContinuousAlternatingMap.alternatizeUncurryFin (𝕜 := ℝ) (F := ℂ) B).wedgeℂ A) w₂ := by
      simpa using
        congrArg
          (fun t =>
            ((ContinuousAlternatingMap.alternatizeUncurryFin (𝕜 := ℝ) (F := ℂ) B).wedgeℂ A) t)
          hw2
    -- `wedgeAlternating` here refers to the *scalar-valued* wedge; we stay in `wedgeℂ`.
    have hwedge2 :
        ContinuousAlternatingMap.wedgeℂ (E := TangentModel n)
            (ContinuousAlternatingMap.alternatizeUncurryFin (𝕜 := ℝ) (F := ℂ) B) A w₂ =
          (ContinuousAlternatingMap.alternatizeUncurryFin (𝕜 := ℝ) (F := ℂ) B).wedgeℂ A w₂ := by
      rfl
    -- Rewrite the LHS using `hperm` (unfolding `altB` and rewriting the vectors to `w₁`/`w₂`).
    have hperm' :
        ((ContinuousAlternatingMap.alternatizeUncurryFin (𝕜 := ℝ) (F := ℂ) B).wedgeℂ A) w₁ =
          (Equiv.Perm.sign σ : ℤˣ) •
            ((ContinuousAlternatingMap.alternatizeUncurryFin (𝕜 := ℝ) (F := ℂ) B).wedgeℂ A) w₂ := by
      simpa [altB, w₁, w₂] using hperm
    -- Use `hperm'` and rewrite the auxiliary definitional equality `hwedge2` (no-op).
    rw [hperm']
    rw [hwedge2]
    -- Convert the unit action and close using `hσsign`/`hpar`,
    -- then transport the RHS argument using `hw2_val`.
    have hpar' :
        (-1 : ℂ) ^ (l * (k' + 1)) * (-1 : ℂ) ^ ((l + 1) * (k' + 1)) = (-1 : ℂ) ^ (k' + 1) := by
      -- `hpar` was proved with the factors in the opposite order.
      simpa [Nat.mul_comm (k' + 1) l] using hpar
    have hRHS :
        (-1 : ℂ) ^ (k' + 1) *
            ((ContinuousAlternatingMap.alternatizeUncurryFin (𝕜 := ℝ) (F := ℂ) B).wedgeℂ A) w₂ =
          (-1 : ℂ) ^ (k' + 1) *
            ((ContinuousAlternatingMap.alternatizeUncurryFin (𝕜 := ℝ) (F := ℂ) B).wedgeℂ A)
              ((v ∘ ⇑(Equiv.refl (Fin (k' + 1 + (l + 1))))) ∘
                ⇑(blockSwapEquiv (k' + 1) (l + 1)).symm) := by
      simpa [mul_assoc] using
        congrArg (fun z => (-1 : ℂ) ^ (k' + 1) * z) hw2_val.symm
    have hLHS :
        (-1 : ℂ) ^ (l * (k' + 1)) *
            ((Equiv.Perm.sign σ : ℤˣ) •
              ((ContinuousAlternatingMap.alternatizeUncurryFin (𝕜 := ℝ) (F := ℂ) B).wedgeℂ A) w₂) =
          (-1 : ℂ) ^ (k' + 1) *
            ((ContinuousAlternatingMap.alternatizeUncurryFin (𝕜 := ℝ) (F := ℂ) B).wedgeℂ A) w₂ := by
      -- Write the common factor as `z` to keep the algebra readable.
      set z : ℂ :=
        ((ContinuousAlternatingMap.alternatizeUncurryFin (𝕜 := ℝ) (F := ℂ) B).wedgeℂ A) w₂
      -- Convert the unit action to multiplication, then use `hpar'` to combine the `(-1)^…` factors.
      calc
        (-1 : ℂ) ^ (l * (k' + 1)) * ((Equiv.Perm.sign σ : ℤˣ) • z)
            = (-1 : ℂ) ^ (l * (k' + 1)) * ((-1 : ℂ) ^ ((l + 1) * (k' + 1)) * z) := by
                -- `hσsign` identifies `sign σ` as a `(-1)`-power in `ℂ`.
                simp [z, Units.smul_def, zsmul_eq_mul, hσsign, mul_assoc]
        _ = ((-1 : ℂ) ^ (l * (k' + 1)) * (-1 : ℂ) ^ ((l + 1) * (k' + 1))) * z := by
              simpa [mul_assoc] using
                (mul_assoc ((-1 : ℂ) ^ (l * (k' + 1)))
                  ((-1 : ℂ) ^ ((l + 1) * (k' + 1))) z).symm
        _ = (-1 : ℂ) ^ (k' + 1) * z := by
              have := congrArg (fun t => t * z) hpar'
              simpa [mul_assoc] using this
      -- `set z := ...` already rewrote the goal, so nothing further to do.
    exact hLHS.trans hRHS

/-- Main theorem: alternatization commutes with wedge when left factor is constant. -/
theorem alternatizeUncurryFin_wedge_left {k l : ℕ}
    (A : Alt n k) (B : TangentModel n →L[ℝ] Alt n l) :
    let wedge_left : TangentModel n →L[ℝ] Alt n (k + l) :=
      (ContinuousAlternatingMap.wedgeℂCLM_alt (E := TangentModel n) k l A) ∘L B
    ContinuousAlternatingMap.alternatizeUncurryFin (𝕜 := ℝ) (F := ℂ) wedge_left =
    ContinuousAlternatingMap.domDomCongr
      ((-1 : ℂ)^k • A.wedgeℂ (ContinuousAlternatingMap.alternatizeUncurryFin (𝕜 := ℝ) (F := ℂ) B))
      (finCongr (show k+(l+1) = (k+l)+1 by omega)) := by
  intro wedge_left
  ext v
  simp only [ContinuousAlternatingMap.alternatizeUncurryFin_apply,
             ContinuousAlternatingMap.domDomCongr_apply]
  -- Use the shuffle bijection lemma
  have h_wedge_left : ∀ w, wedge_left w = A.wedgeℂ (B w) := fun _ => rfl
  simp only [h_wedge_left]
  exact shuffle_bijection_left v A B

/-! ### The Leibniz Rule -/

/-- Cast a `ContinuousAlternatingMap` along an equality of the index cardinality. -/
noncomputable def castAlt {m m' : ℕ} (h : m = m') (f : Alt n m) : Alt n m' :=
  ContinuousAlternatingMap.domDomCongr f (finCongr h)

/-- **Leibniz rule for exterior derivative**: d(ω ∧ η) = dω ∧ η + (-1)^k ω ∧ dη.

This is the fundamental identity relating the exterior derivative to the wedge product.
It expresses that d is a graded derivation on the exterior algebra.
-/
theorem extDerivAt_wedge {k l : ℕ} (ω : ContMDiffForm n X k) (η : ContMDiffForm n X l) (x : X) :
    ContMDiffForm.extDerivAt (ω.wedge η) x =
    castAlt (show (k+1)+l = (k+l)+1 by omega)
      ((ContMDiffForm.extDerivAt ω x).wedgeℂ (η.as_alternating x)) +
    castAlt (show k+(l+1) = (k+l)+1 by omega)
      (((-1 : ℂ)^k) • (ω.as_alternating x).wedgeℂ (ContMDiffForm.extDerivAt η x)) := by
  classical
  -- Unfold `extDerivAt` and the pointwise `wedge` definition.
  simp only [ContMDiffForm.extDerivAt, ContMDiffForm.wedge]

  -- Abbreviate the derivative and value terms.
  let A_ω : TangentModel n →L[ℝ] Alt n k :=
    mfderiv (𝓒_complex n) 𝓘(ℝ, Alt n k) ω.as_alternating x
  let B_η : Alt n l := η.as_alternating x
  let A_η : TangentModel n →L[ℝ] Alt n l :=
    mfderiv (𝓒_complex n) 𝓘(ℝ, Alt n l) η.as_alternating x
  let B_ω : Alt n k := ω.as_alternating x

  -- Express the manifold derivative of the wedge as a sum of two “wedge with a fixed factor” maps.
  let wedge_right : TangentModel n →L[ℝ] Alt n (k + l) :=
    (ContinuousAlternatingMap.wedgeℂCLM_alt (E := TangentModel n) k l).flip B_η ∘L A_ω
  let wedge_left : TangentModel n →L[ℝ] Alt n (k + l) :=
    (ContinuousAlternatingMap.wedgeℂCLM_alt (E := TangentModel n) k l B_ω) ∘L A_η
  have hmf :
      mfderiv (𝓒_complex n) 𝓘(ℝ, Alt n (k + l))
          (fun y => ContinuousAlternatingMap.wedgeℂ (E := TangentModel n) (ω.as_alternating y) (η.as_alternating y))
          x =
        wedge_right + wedge_left := by
    ext v
    -- `mfderiv_wedge_apply` gives the Leibniz formula pointwise.
    simpa [wedge_right, wedge_left, A_ω, A_η, B_ω, B_η, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply, ContinuousAlternatingMap.wedgeℂCLM_alt]
      using (mfderiv_wedge_apply (n := n) (X := X) (k := k) (l := l) ω η x v)

  -- Rewrite the derivative using `hmf` and alternatize term-by-term.
  rw [hmf]
  rw [ContinuousAlternatingMap.alternatizeUncurryFin_add]

  -- Apply the two combinatorial lemmas.
  -- Right term: dω ∧ η
  have hR0 :=
    alternatizeUncurryFin_wedge_right (n := n) (k := k) (l := l) (A := A_ω) (B := B_η)
  have hR :
      ContinuousAlternatingMap.alternatizeUncurryFin (𝕜 := ℝ) (F := ℂ) wedge_right =
        ContinuousAlternatingMap.domDomCongr
          ((ContinuousAlternatingMap.alternatizeUncurryFin (𝕜 := ℝ) (F := ℂ) A_ω).wedgeℂ B_η)
          (finCongr (show (k + 1) + l = (k + l) + 1 by omega)) := by
    simpa [wedge_right] using hR0
  -- Left term: (-1)^k ω ∧ dη
  have hL0 :=
    alternatizeUncurryFin_wedge_left (n := n) (k := k) (l := l) (A := B_ω) (B := A_η)
  have hL :
      ContinuousAlternatingMap.alternatizeUncurryFin (𝕜 := ℝ) (F := ℂ) wedge_left =
        ContinuousAlternatingMap.domDomCongr
          (((-1 : ℂ) ^ k) • B_ω.wedgeℂ
              (ContinuousAlternatingMap.alternatizeUncurryFin (𝕜 := ℝ) (F := ℂ) A_η))
          (finCongr (show k + (l + 1) = (k + l) + 1 by omega)) := by
    simpa [wedge_left] using hL0

  -- Rewrite both summands and finish: `castAlt` is `domDomCongr` along `finCongr`.
  rw [hR, hL]
  simp [castAlt, A_ω, A_η, B_ω, B_η]

end LeibnizRule
