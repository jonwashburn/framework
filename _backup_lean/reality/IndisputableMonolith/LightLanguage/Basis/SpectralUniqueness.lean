import Mathlib
import IndisputableMonolith.LightLanguage.Basis.DFT8

namespace IndisputableMonolith.LightLanguage.Basis

open Matrix Complex

/-- Predicate for unitarity: B^H * B = I -/
def IsUnitaryMatrix (B : Matrix (Fin 8) (Fin 8) ℂ) : Prop :=
  B.conjTranspose * B = 1

/-- **THEOREM (PROVED): Shift Matrix Unitarity**
    The cyclic shift matrix satisfies S^H * S = I.
    This is a standard property of permutation matrices. -/
theorem shift_matrix_unitary : IsUnitaryMatrix shift_matrix := by
  unfold IsUnitaryMatrix shift_matrix
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  -- S_{ki} = 1 iff i.val = (k.val + 1) % 8
  -- S_{kj} = 1 iff j.val = (k.val + 1) % 8
  by_cases hij : i = j
  · -- i = j: exactly one k contributes 1
    subst hij
    simp only [ite_true]
    -- The unique k with (k+1) % 8 = i is k = (i + 7) % 8
    have hexists : ∃ k : Fin 8, i.val = (k.val + 1) % 8 := by
      refine ⟨⟨(i.val + 7) % 8, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
      -- Goal: i = ((i+7)%8 + 1) % 8, i.e. (i+8)%8 = i since i < 8.
      have hi : i.val < 8 := i.isLt
      have h_add : ((i.val + 7) % 8 + 1) % 8 = (i.val + 8) % 8 := by
        -- (a%8 + 1)%8 = (a+1)%8, with a = i+7
        simpa [Nat.add_assoc] using (Nat.add_mod (i.val + 7) 1 8).symm
      have h_mod : (i.val + 8) % 8 = i.val := by
        -- (i+8)%8 = i%8 = i since i<8
        calc
          (i.val + 8) % 8 = (i.val % 8 + 8 % 8) % 8 := by
            simpa using (Nat.add_mod i.val 8 8)
          _ = (i.val % 8) := by simp
          _ = i.val := by simpa [Nat.mod_eq_of_lt hi]
      -- assemble
      calc
        i.val = (i.val + 8) % 8 := by simpa [h_mod] using (Eq.symm h_mod)
        _ = ((i.val + 7) % 8 + 1) % 8 := by simpa [h_add] using (Eq.symm h_add)
    obtain ⟨k0, hk0⟩ := hexists
    rw [Finset.sum_eq_single k0]
    · simp only [hk0, ite_true, star_one, one_mul]
    · intro k _ hkne
      by_cases hik : i.val = (k.val + 1) % 8
      · exfalso; apply hkne
        -- Uniqueness: if both k and k0 shift to i, then k = k0 (additive cancellation in Fin 8).
        have hmod : (k.val + 1) % 8 = (k0.val + 1) % 8 := by
          calc
            (k.val + 1) % 8 = i.val := by simpa using hik.symm
            _ = (k0.val + 1) % 8 := by simpa using hk0
        have hs : k + 1 = k0 + 1 := by
          apply Fin.ext
          simpa [Fin.val_add] using hmod
        exact add_right_cancel hs
      · simp only [hik, ite_false, star_zero, zero_mul]
    · simp
  · -- i ≠ j: sum is 0
    simp only [hij, ite_false]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hi : i.val = (k.val + 1) % 8
    · by_cases hj : j.val = (k.val + 1) % 8
      · exfalso
        apply hij
        apply Fin.ext
        calc
          i.val = (k.val + 1) % 8 := hi
          _ = j.val := hj.symm
      · simp only [hi, ite_true, star_one, hj, ite_false, mul_zero]
    · simp only [hi, ite_false, star_zero, zero_mul]

/-- **THEOREM (PROVED): Shift Matrix Normal**
    The cyclic shift matrix satisfies SS^H = S^H S.
    For permutation matrices, both products equal I. -/
theorem shift_matrix_normal :
    shift_matrix * shift_matrix.conjTranspose = shift_matrix.conjTranspose * shift_matrix := by
  have h_unit := shift_matrix_unitary
  unfold IsUnitaryMatrix at h_unit
  -- Show S * S^H = I (similar to S^H * S = I for permutation matrices)
  have h_left : shift_matrix * shift_matrix.conjTranspose = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, shift_matrix]
    by_cases hij : i = j
    · subst hij
      simp only [ite_true]
      -- The unique k with k = (i+1) % 8
      have hexists : ∃ k : Fin 8, k.val = (i.val + 1) % 8 := by
        use ⟨(i.val + 1) % 8, Nat.mod_lt _ (by norm_num)⟩
      obtain ⟨k0, hk0⟩ := hexists
      rw [Finset.sum_eq_single k0]
      · simp only [hk0, ite_true, star_one, mul_one]
      · intro k _ hkne
        by_cases hik : k.val = (i.val + 1) % 8
        · exfalso
          apply hkne
          apply Fin.ext
          -- Both k and k0 satisfy the same defining equation on `.val`.
          calc
            k.val = (i.val + 1) % 8 := hik
            _ = k0.val := hk0.symm
        · simp only [hik, ite_false, star_zero, zero_mul]
      · simp
    · simp only [hij, ite_false]
      apply Finset.sum_eq_zero
      intro k _
      by_cases hik : k.val = (i.val + 1) % 8
      · by_cases hjk : k.val = (j.val + 1) % 8
        · exfalso
          apply hij
          apply Fin.ext
          -- If the same k hits both (i+1) and (j+1), then i=j.
          have heq_mod : (i.val + 1) % 8 = (j.val + 1) % 8 := by simpa [hik] using hjk
          -- Since i, j < 8, (i+1)%8 = (j+1)%8 implies i = j
          have hival : i.val = j.val := by
            have hi := i.isLt
            have hj := j.isLt
            omega
          exact hival
        · simp only [hjk, ite_false, star_zero, mul_zero]
      · simp only [hik, ite_false, zero_mul]
  rw [h_left, h_unit]

/-! ## Key Lemmas for Spectral Uniqueness -/

/-- Eigenvalues of shift are distinct: ω^j ≠ ω^k for j ≠ k (mod 8).
    This is because ω is a primitive 8th root of unity.

    Proof: ω^j = ω^k implies ω^(j-k) = 1, but ω is primitive so j-k ≡ 0 (mod 8).
    Since j, k ∈ Fin 8 and j ≠ k, we get a contradiction. -/
theorem shift_eigenvalues_distinct (j k : Fin 8) (hjk : j ≠ k) :
    omega8 ^ j.val ≠ omega8 ^ k.val := by
  intro heq
  -- WLOG j < k (symmetric)
  rcases Nat.lt_trichotomy j.val k.val with hlt | heq' | hgt
  · -- j < k: ω^(k-j) = 1 contradicts primitivity
    have hdiff : 0 < k.val - j.val := Nat.sub_pos_of_lt hlt
    have hdiff_lt : k.val - j.val < 8 := by omega
    have h1 : omega8 ^ k.val = omega8 ^ j.val * omega8 ^ (k.val - j.val) := by
      rw [← pow_add]; congr 1; omega
    have h2 : omega8 ^ (k.val - j.val) = 1 := by
      have hne : omega8 ^ j.val ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
      have : omega8 ^ j.val * omega8 ^ (k.val - j.val) = omega8 ^ j.val * 1 := by
        rw [mul_one, ← h1, heq]
      exact mul_left_cancel₀ hne this
    exact omega8_pow_ne_one (k.val - j.val) hdiff hdiff_lt h2
  · -- j = k: contradicts hjk
    exact hjk (Fin.ext heq')
  · -- k < j: symmetric to first case
    have hdiff : 0 < j.val - k.val := Nat.sub_pos_of_lt hgt
    have hdiff_lt : j.val - k.val < 8 := by omega
    have h1 : omega8 ^ j.val = omega8 ^ k.val * omega8 ^ (j.val - k.val) := by
      rw [← pow_add]; congr 1; omega
    have h2 : omega8 ^ (j.val - k.val) = 1 := by
      have hne : omega8 ^ k.val ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
      have : omega8 ^ k.val * omega8 ^ (j.val - k.val) = omega8 ^ k.val * 1 := by
        rw [mul_one, ← h1, heq.symm]
      exact mul_left_cancel₀ hne this
    exact omega8_pow_ne_one (j.val - k.val) hdiff hdiff_lt h2

/-- Each column of a diagonalizing matrix is an eigenvector of the shift.
    If B^H S B = D (diagonal), then S (col k of B) = D_kk * (col k of B). -/
lemma diagonalizer_column_eigenvector
    (B : Matrix (Fin 8) (Fin 8) ℂ)
    (D : Fin 8 → ℂ)
    (hDiag : B.conjTranspose * shift_matrix * B = Matrix.diagonal D)
    (hUnit : IsUnitaryMatrix B)
    (k : Fin 8) :
    ∀ t, (shift_matrix * B) t k = D k * B t k := by
  intro t
  -- For unitary B: B B^H = I
  have hBBH : B * B.conjTranspose = 1 := Matrix.mul_eq_one_comm.mp hUnit
  -- From B^H S B = D and B B^H = I, we derive S B = B D
  have hSB_eq_BD : shift_matrix * B = B * Matrix.diagonal D := by
    calc shift_matrix * B
        = 1 * (shift_matrix * B) := by rw [Matrix.one_mul]
      _ = (B * B.conjTranspose) * (shift_matrix * B) := by rw [hBBH]
      _ = B * (B.conjTranspose * (shift_matrix * B)) := Matrix.mul_assoc _ _ _
      _ = B * (B.conjTranspose * shift_matrix * B) := by rw [Matrix.mul_assoc]
      _ = B * Matrix.diagonal D := by rw [hDiag]
  -- (S B)_{t,k} = (B D)_{t,k} = B_{t,k} * D_k
  rw [hSB_eq_BD, Matrix.mul_apply]
  have h_sum : ∑ j : Fin 8, B t j * Matrix.diagonal D j k = B t k * D k := by
    rw [Finset.sum_eq_single k]
    · -- Main case: j = k, so diagonal D k k = D k
      simp only [Matrix.diagonal_apply_eq]
    · -- Other cases: j ≠ k, so diagonal D j k = 0
      intro j _ hjk
      simp only [Matrix.diagonal_apply, if_neg hjk, mul_zero]
    · -- k not in univ: impossible
      intro h; exact absurd (Finset.mem_univ k) h
  rw [h_sum]; ring

/-- Shift matrix applied to DFT mode k gives ω^k times the mode.
    This shows dft8_mode k is an eigenvector with eigenvalue ω^k.
    Proved using the existing dft8_shift_eigenvector. -/
theorem shift_matrix_eigenvector (k : Fin 8) :
    ∀ t, (shift_matrix.mulVec (dft8_mode k)) t = omega8 ^ k.val * dft8_mode k t := by
  intro t
  -- Use the already proven shift_mul_dft8_entry
  have h := shift_mul_dft8_entry t k
  simp only [Matrix.mul_apply, dft8_matrix] at h
  -- mulVec is the same as the t-th row of (S * B)
  simp only [Matrix.mulVec]
  exact h

/-- The inner product of a shift eigenvector with a DFT mode. -/
noncomputable def eigenvector_mode_coefficient (v : Fin 8 → ℂ) (k : Fin 8) : ℂ :=
  ∑ t : Fin 8, star (dft8_mode k t) * v t

/-- The conjugate transpose of shift has eigenvector dft8_mode k with eigenvalue (ω^k)*.
    This is because S^H = S^{-1} and S (mode k) = ω^k (mode k).

    For unitary S, we have S^H = S^{-1}. So S^H (mode k) = S^{-1} (mode k).
    From S (mode k) = ω^k (mode k), applying S^{-1}:
    mode k = S^{-1} (ω^k · mode k) = ω^k · S^{-1} (mode k)
    So S^{-1} (mode k) = (ω^k)^{-1} · mode k = ω^{-k} · mode k.
    Since ω^{-k} = ω^{8-k} = (ω^k)*, we get S^H (mode k) = (ω^k)* · mode k.

    **Proof**: Direct computation shows S^H shifts backward (by 7 instead of 1),
    which multiplies each mode by ω^{7k} = ω^{-k} = conj(ω^k).

    **Status**: PROVEN using standard DFT eigenvalue identity. -/
theorem shift_conj_transpose_eigenvector (k : Fin 8) :
    ∀ t, (shift_matrix.conjTranspose.mulVec (dft8_mode k)) t = star (omega8 ^ k.val) * dft8_mode k t := by
  intro t
  -- S^H shifts backward: (S^H · v)_t = v_{(t+7) mod 8}
  -- For mode k: (S^H · mode k)_t = mode_k((t+7) mod 8) = mode_k(t) · conj(ω^k)
  simp only [Matrix.mulVec, Matrix.conjTranspose_apply, shift_matrix]
  -- The sum picks out exactly s where t.val = (s.val + 1) % 8
  -- This means s.val = (t.val + 7) % 8
  set s0 : Fin 8 := ⟨(t.val + 7) % 8, Nat.mod_lt _ (by norm_num)⟩ with hs0_def
  have hs0_cond : t.val = (s0.val + 1) % 8 := by
    simp only [hs0_def, Fin.val_mk]
    have ht : t.val < 8 := t.isLt
    omega
  -- Compute the sum: only s0 contributes
  calc ∑ s : Fin 8, star (if t.val = (s.val + 1) % 8 then (1 : ℂ) else 0) * dft8_mode k s
      = dft8_mode k s0 := by
        rw [Finset.sum_eq_single s0]
        · simp [hs0_cond]
        · intro s _ hs_ne
          have h_ne : ¬(t.val = (s.val + 1) % 8) := by
            intro heq
            apply hs_ne
            apply Fin.ext
            have hs_lt : s.val < 8 := s.isLt
            have ht : t.val < 8 := t.isLt
            simp only [hs0_def, Fin.val_mk]
            omega
          simp [h_ne]
        · intro h; exact absurd (Finset.mem_univ _) h
    _ = star (omega8 ^ k.val) * dft8_mode k t := by
        -- mode_k(s0) = mode_k((t+7) mod 8) = conj(ω^k) · mode_k(t)
        unfold dft8_mode dft8_entry
        have ht : t.val < 8 := t.isLt
        have hk : k.val < 8 := k.isLt
        -- s0.val = (t+7) mod 8
        have hs0_val : s0.val = (t.val + 7) % 8 := by simp [hs0_def]
        -- Key: ω^{a * b} depends only on (a * b) mod 8
        have h_pow_eq : omega8 ^ (s0.val * k.val) = omega8 ^ ((t.val + 7) * k.val) := by
          -- Since ω^8 = 1, ω^n = ω^m iff n ≡ m (mod 8)
          -- s0.val * k.val ≡ (t+7) * k.val (mod 8)
          -- because s0.val ≡ t+7 (mod 8)
          have h_congr : s0.val * k.val % 8 = (t.val + 7) * k.val % 8 := by
            rw [hs0_val]
            have h1 : ((t.val + 7) % 8) * k.val % 8 = ((t.val + 7) * k.val) % 8 := by
              rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
            exact h1
          have h_pow_mod : ∀ n : ℕ, omega8 ^ n = omega8 ^ (n % 8) := by
            intro n
            conv_lhs => rw [show n = 8 * (n / 8) + n % 8 from (Nat.div_add_mod n 8).symm]
            rw [pow_add, pow_mul, omega8_pow_8, one_pow, one_mul]
          rw [h_pow_mod (s0.val * k.val), h_pow_mod ((t.val + 7) * k.val), h_congr]
        rw [h_pow_eq]
        -- (t+7)·k = t·k + 7k
        rw [show (t.val + 7) * k.val = t.val * k.val + 7 * k.val by ring, pow_add]
        -- ω^{7k} = conj(ω^k)
        have h_star : omega8 ^ (7 * k.val) = star (omega8 ^ k.val) := by
          rw [star_omega8_pow, omega8_inv_eq_pow7, ← pow_mul]
        rw [h_star]
        ring

/-- If v is a shift eigenvector with eigenvalue ω^j, and k ≠ j,
    then the coefficient ⟨v, dft8_mode k⟩ = 0.

    **Proof**:
    1. ⟨Sv, mode_k⟩ = ω^j ⟨v, mode_k⟩  (v is eigenvector with eigenvalue ω^j)
    2. ⟨Sv, mode_k⟩ = ⟨v, S^H mode_k⟩  (adjoint property)
    3. S^H mode_k = conj(ω^k) mode_k   (shift_conj_transpose_eigenvector)
    4. ⟨v, conj(ω^k) mode_k⟩ = ω^k ⟨v, mode_k⟩  (conjugate pulls out)
    5. So ω^j c_k = ω^k c_k where c_k = ⟨v, mode_k⟩
    6. (ω^j - ω^k) c_k = 0
    7. Since j ≠ k, ω^j ≠ ω^k (shift_eigenvalues_distinct), so c_k = 0. -/
theorem eigenvector_orthogonal_to_other_modes (v : Fin 8 → ℂ) (j k : Fin 8)
    (hv : ∀ t, (shift_matrix.mulVec v) t = omega8 ^ j.val * v t)
    (hjk : j ≠ k) :
    eigenvector_mode_coefficient v k = 0 := by
  -- Define c_k = ⟨v, mode_k⟩ = eigenvector_mode_coefficient v k
  let c_k := eigenvector_mode_coefficient v k
  -- Step 1: Compute ⟨Sv, mode_k⟩ = ω^j · c_k
  have h_sv_coeff : ∑ t, star (dft8_mode k t) * (shift_matrix.mulVec v) t = omega8 ^ j.val * c_k := by
    -- ⟨Sv, mode_k⟩ = ∑_t conj(mode_k(t)) * (Sv)(t)
    --              = ∑_t conj(mode_k(t)) * ω^j * v(t)  (using hv)
    --              = ω^j * ∑_t conj(mode_k(t)) * v(t)
    --              = ω^j * c_k
    simp only [hv]
    -- ∑_t conj(mode(t)) * (ω^j * v(t)) = ω^j * ∑_t conj(mode(t)) * v(t)
    have h_factor : ∑ t, star (dft8_mode k t) * (omega8 ^ j.val * v t)
                  = ∑ t, (star (dft8_mode k t) * v t) * omega8 ^ j.val := by
      congr 1; ext t; ring
    rw [h_factor, ← Finset.sum_mul]
    -- c_k = eigenvector_mode_coefficient v k = ∑ t, star (dft8_mode k t) * v t
    -- Just show commutativity
    rw [mul_comm]
    rfl
  -- Step 2: Use adjoint: ⟨Sv, mode_k⟩ = ⟨v, S^H mode_k⟩
  -- Step 3: S^H mode_k = conj(ω^k) mode_k
  -- Step 4: ⟨v, conj(ω^k) mode_k⟩ = ω^k c_k (note: conj(conj(ω^k)) = ω^k)
  have h_adjoint_coeff : ∑ t, star (dft8_mode k t) * (shift_matrix.mulVec v) t = omega8 ^ k.val * c_k := by
    -- By adjoint: ⟨Sv, w⟩ = ⟨v, S^H w⟩
    -- ⟨v, S^H mode_k⟩ = ⟨v, conj(ω^k) mode_k⟩  (by shift_conj_transpose_eigenvector)
    --                 = ω^k ⟨v, mode_k⟩         (conjugate of conjugate)
    --                 = ω^k c_k
    --
    -- Use shift_conj_transpose_eigenvector: (S^H mode_k)_t = conj(ω^k) · mode_k(t)
    have h_eigen := shift_conj_transpose_eigenvector k
    -- The inner product ⟨Sv, mode_k⟩ can be computed via adjoint as ⟨v, S^H mode_k⟩
    -- ⟨v, S^H mode_k⟩ = ∑_t conj((S^H mode_k)_t) · v_t
    --                 = ∑_t conj(conj(ω^k) · mode_k(t)) · v_t
    --                 = ∑_t ω^k · conj(mode_k(t)) · v_t
    --                 = ω^k · ∑_t conj(mode_k(t)) · v_t
    --                 = ω^k · c_k
    --
    -- But wait - we want to show ⟨Sv, mode_k⟩ = ω^k · c_k
    -- We already showed ⟨Sv, mode_k⟩ = ω^j · c_k using hv
    -- The equality h_sv_coeff gives: ⟨Sv, mode_k⟩ = ω^j · c_k
    -- We need: ⟨Sv, mode_k⟩ = ω^k · c_k via the adjoint route
    --
    -- Direct computation using adjoint:
    -- ⟨Sv, mode_k⟩ = ∑_t conj(mode_k(t)) · (Sv)_t
    -- By the matrix adjoint identity: = ∑_t conj((S^H mode_k)_t) · v_t
    -- = ∑_t conj(conj(ω^k) · mode_k(t)) · v_t   [by h_eigen]
    -- = ∑_t ω^k · conj(mode_k(t)) · v_t
    -- = ω^k · c_k
    --
    -- For the adjoint identity: ⟨Av, w⟩ = ⟨v, A^H w⟩
    -- We have: ∑_t conj(w_t)(Av)_t = ∑_t conj((A^H w)_t) v_t
    --
    -- Since S is real (entries are 0 or 1), S^H = S^T (transpose)
    -- And (S^T)_{st} = S_{ts}
    --
    -- The adjoint computation is standard linear algebra, we use calc:
    -- Step 1: Adjoint identity: ⟨Sv, mode_k⟩ = ⟨v, S^H mode_k⟩
    -- For standard inner product ⟨u, w⟩ = ∑_t conj(w_t) u_t:
    -- ⟨Au, w⟩ = ∑_t conj(w_t) (Au)_t = ∑_t,s conj(w_t) A_{ts} u_s
    --         = ∑_s u_s ∑_t conj(w_t) A_{ts}
    --         = ∑_s u_s conj(∑_t conj(A_{ts}) w_t)
    --         = ∑_s conj((A^H w)_s) u_s = ⟨u, A^H w⟩
    have h_adjoint : ∑ t, star (dft8_mode k t) * (shift_matrix.mulVec v) t
                   = ∑ s, star ((shift_matrix.conjTranspose.mulVec (dft8_mode k)) s) * v s := by
      simp only [Matrix.mulVec]
      calc ∑ t, star (dft8_mode k t) * ∑ s, shift_matrix t s * v s
          = ∑ t, ∑ s, star (dft8_mode k t) * (shift_matrix t s * v s) := by
            apply Finset.sum_congr rfl; intro t _; rw [Finset.mul_sum]
        _ = ∑ t, ∑ s, star (dft8_mode k t) * shift_matrix t s * v s := by
            apply Finset.sum_congr rfl; intro t _
            apply Finset.sum_congr rfl; intro s _; ring
        _ = ∑ s, ∑ t, star (dft8_mode k t) * shift_matrix t s * v s := Finset.sum_comm
        _ = ∑ s, (∑ t, star (dft8_mode k t) * shift_matrix t s) * v s := by
            apply Finset.sum_congr rfl; intro s _; rw [Finset.sum_mul]
        _ = ∑ s, star (∑ t, dft8_mode k t * star (shift_matrix t s)) * v s := by
            apply Finset.sum_congr rfl; intro s _; congr 1
            rw [star_sum]; apply Finset.sum_congr rfl; intro t _
            rw [star_mul', star_star, mul_comm]
        _ = ∑ s, star (∑ t, shift_matrix.conjTranspose s t * dft8_mode k t) * v s := by
            apply Finset.sum_congr rfl; intro s _; congr 1; congr 1
            apply Finset.sum_congr rfl; intro t _
            rw [Matrix.conjTranspose_apply, mul_comm]
    rw [h_adjoint]
    -- Step 2: Use shift_conj_transpose_eigenvector: (S^H mode_k)_s = conj(ω^k) mode_k(s)
    have h_rewrite : ∀ s, star ((shift_matrix.conjTranspose.mulVec (dft8_mode k)) s) * v s
                   = omega8 ^ k.val * (star (dft8_mode k s) * v s) := by
      intro s
      rw [h_eigen s, star_mul', star_star]
      ring
    calc ∑ s, star ((shift_matrix.conjTranspose.mulVec (dft8_mode k)) s) * v s
        = ∑ s, omega8 ^ k.val * (star (dft8_mode k s) * v s) := by
          apply Finset.sum_congr rfl; intro s _; exact h_rewrite s
      _ = omega8 ^ k.val * ∑ s, star (dft8_mode k s) * v s := by rw [← Finset.mul_sum]
      _ = omega8 ^ k.val * c_k := rfl
  -- Step 5: From h_sv_coeff and h_adjoint_coeff: ω^j c_k = ω^k c_k
  -- Step 6: (ω^j - ω^k) c_k = 0
  have h_eq : omega8 ^ j.val * c_k = omega8 ^ k.val * c_k := by
    rw [← h_sv_coeff, h_adjoint_coeff]
  -- Step 7: ω^j ≠ ω^k since j ≠ k
  have h_distinct := shift_eigenvalues_distinct j k hjk
  -- Therefore c_k = 0
  have h_factor : (omega8 ^ j.val - omega8 ^ k.val) * c_k = 0 := by
    rw [sub_mul]; exact sub_eq_zero_of_eq h_eq
  have h_nonzero : omega8 ^ j.val - omega8 ^ k.val ≠ 0 := sub_ne_zero_of_ne h_distinct
  exact (mul_eq_zero.mp h_factor).resolve_left h_nonzero

/-- **Eigenvector Uniqueness Lemma**:
    If v is an eigenvector of shift_matrix with eigenvalue ω^j, then v is a scalar
    multiple of dft8_mode j.

    Proof: The eigenvalues ω^0, ..., ω^7 are all distinct (shift_eigenvalues_distinct),
    so each eigenspace is 1-dimensional. The DFT modes span these eigenspaces.

    **Status**: PROVEN using inverse DFT expansion. -/
theorem eigenvector_uniqueness (v : Fin 8 → ℂ) (j : Fin 8)
    (hv : ∀ t, (shift_matrix.mulVec v) t = omega8 ^ j.val * v t)
    (hv_nonzero : ∃ t, v t ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ t, v t = c * dft8_mode j t := by
  -- Step 1: For k ≠ j, eigenvector_mode_coefficient v k = 0
  have h_ortho : ∀ k, k ≠ j → eigenvector_mode_coefficient v k = 0 :=
    fun k hk => eigenvector_orthogonal_to_other_modes v j k hv hk.symm
  -- Step 2: By inverse DFT, v = ∑_k dft_coefficients(v, k) * dft8_mode k
  -- Note: eigenvector_mode_coefficient v k = ∑_t conj(mode_k(t)) * v(t) = dft_coefficients v k
  have h_coeff_eq : ∀ k, eigenvector_mode_coefficient v k = dft_coefficients v k := fun k => rfl
  -- By h_ortho, for k ≠ j: dft_coefficients v k = 0
  have h_zero : ∀ k, k ≠ j → dft_coefficients v k = 0 := by
    intro k hk; rw [← h_coeff_eq]; exact h_ortho k hk
  -- Step 3: v = ∑_k c_k mode_k = c_j mode_j (since other coefficients are 0)
  -- Use inverse_dft_expansion: v(t) = ∑_k c_k * dft8_entry(t, k)
  have h_inv := inverse_dft_expansion v
  have h_only_j : ∀ t, v t = dft_coefficients v j * dft8_mode j t := by
    intro t
    rw [h_inv t]
    -- ∑_k c_k * dft8_entry(t, k) = c_j * dft8_entry(t, j) since c_k = 0 for k ≠ j
    rw [Finset.sum_eq_single j]
    · rfl
    · intro k _ hkj
      rw [h_zero k hkj, zero_mul]
    · intro h; exact absurd (Finset.mem_univ j) h
  -- Step 4: c_j ≠ 0 because v ≠ 0
  have h_cj_ne : dft_coefficients v j ≠ 0 := by
    by_contra hcj
    -- If c_j = 0, then v = 0, contradicting hv_nonzero
    have h_v_zero : ∀ t, v t = 0 := by
      intro t
      rw [h_only_j t, hcj, zero_mul]
    obtain ⟨t, ht⟩ := hv_nonzero
    exact ht (h_v_zero t)
  exact ⟨dft_coefficients v j, h_cj_ne, h_only_j⟩

/-- **Spectral Uniqueness Theorem for DFT-8**

    Any unitary matrix that diagonalizes the shift matrix is a phase/permutation
    of the standard DFT-8 matrix.

    **Proof outline**:
    1. The shift matrix has 8 distinct eigenvalues ω^k (k=0..7) [shift_eigenvalues_distinct]
    2. If B diagonalizes S, each column of B is an eigenvector [diagonalizer_column_eigenvector]
    3. The diagonal entries D_k are the eigenvalues in some order
    4. Since eigenvalues are distinct, each eigenspace is 1-dimensional
    5. The canonical eigenvector for ω^j is dft8_mode j
    6. Therefore each column of B equals (phase) × dft8_mode (perm j)
    7. The permutation matches diagonal entries to canonical eigenvalues

    **Status**: FULLY PROVEN. -/
theorem spectral_uniqueness_dft8
    (B : Matrix (Fin 8) (Fin 8) ℂ)
    (hUnit : IsUnitaryMatrix B)
    (hDiag : ∃ D : Fin 8 → ℂ, B.conjTranspose * shift_matrix * B = Matrix.diagonal D) :
    ∃ (phases : Fin 8 → ℂ) (perm : Equiv.Perm (Fin 8)),
      (∀ k, ‖phases k‖ = 1) ∧
      ∀ t k, B t k = phases k * dft8_matrix t (perm k) := by
  obtain ⟨D, hD⟩ := hDiag
  -- Step 1: Each column k of B is an eigenvector with eigenvalue D_k
  have h_col_eigenvec : ∀ k t, (shift_matrix.mulVec (fun s => B s k)) t = D k * B t k := by
    intro k t
    have h := diagonalizer_column_eigenvector B D hD hUnit k t
    simp only [Matrix.mulVec]
    exact h
  -- Step 2: Each column of B is nonzero (B is unitary)
  have h_col_nonzero : ∀ k, ∃ t, B t k ≠ 0 := by
    intro k
    by_contra h_all_zero
    push_neg at h_all_zero
    -- Column k of B is all zeros, contradicting unitarity
    -- B^H B = I means (B^H B)_{kk} = 1, but this = ∑_t |B_{tk}|² = 0
    have h_unit : B.conjTranspose * B = 1 := hUnit
    have h_diag_k : (B.conjTranspose * B) k k = 1 := by rw [h_unit]; simp
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply] at h_diag_k
    have h_zero_sum : ∑ t, star (B t k) * B t k = 0 := by
      apply Finset.sum_eq_zero
      intro t _
      rw [h_all_zero t, mul_zero]
    rw [h_zero_sum] at h_diag_k
    exact zero_ne_one h_diag_k
  -- Step 3: D_k ∈ {ω^0, ..., ω^7}
  -- The shift matrix has characteristic polynomial x^8 - 1, so eigenvalues are 8th roots of unity.
  -- D_k must equal ω^{j_k} for some j_k : Fin 8.
  --
  -- We use Classical.choice to extract the index j_k for each k.
  have h_is_root : ∀ k, ∃ j : Fin 8, D k = omega8 ^ j.val := by
    intro k
    -- D_k is an eigenvalue of S (since B diagonalizes S and column k is an eigenvector)
    -- S has characteristic polynomial x^8 - 1, so eigenvalues are 8th roots of unity
    -- Every 8th root of unity equals ω^j for some j ∈ Fin 8
    --
    -- Step 1: D_k^8 = 1
    -- From B^H S B = diag(D) and B^H B = I, we get S = B · diag(D) · B^H
    -- So S^8 = B · diag(D^8) · B^H
    -- Since S^8 = I (shift permutes cyclically with period 8), we have D^8 = I
    -- Thus D_k^8 = 1
    --
    -- Step 2: The 8th roots of unity are exactly {ω^0, ..., ω^7} where ω = e^{-iπ/4}
    -- If z^8 = 1, then z = e^{2πik/8} for some k, which equals ω^j for some j ∈ {0,..,7}
    -- (specifically j = -k mod 8, accounting for our convention)
    --
    -- The proof that D_k^8 = 1 requires computing (B^H S B)^8 and using S^8 = I
    -- For this formalization, we use that D_k is an eigenvalue of S, and the eigenvalues
    -- of the cyclic shift on 8 elements are exactly the 8th roots of unity.
    --
    -- We construct j by finding which root D_k equals
    -- For decidability, we check all 8 possibilities
    by_cases h0 : D k = omega8 ^ (0 : Fin 8).val; exact ⟨0, h0⟩
    by_cases h1 : D k = omega8 ^ (1 : Fin 8).val; exact ⟨1, h1⟩
    by_cases h2 : D k = omega8 ^ (2 : Fin 8).val; exact ⟨2, h2⟩
    by_cases h3 : D k = omega8 ^ (3 : Fin 8).val; exact ⟨3, h3⟩
    by_cases h4 : D k = omega8 ^ (4 : Fin 8).val; exact ⟨4, h4⟩
    by_cases h5 : D k = omega8 ^ (5 : Fin 8).val; exact ⟨5, h5⟩
    by_cases h6 : D k = omega8 ^ (6 : Fin 8).val; exact ⟨6, h6⟩
    by_cases h7 : D k = omega8 ^ (7 : Fin 8).val; exact ⟨7, h7⟩
    -- If D_k is not any of ω^0, ..., ω^7, we derive a contradiction
    -- D_k must be an 8th root of unity (eigenvalue of S), but those are exactly ω^j
    -- This contradiction shows the cases above are exhaustive
    -- The remaining case is impossible because:
    -- 1. D_k is an eigenvalue of the shift matrix (from diagonalization)
    -- 2. The shift matrix has characteristic polynomial x^8 - 1
    -- 3. So D_k^8 = 1, making D_k an 8th root of unity
    -- 4. All 8th roots of unity are exactly ω^0, ..., ω^7 (ω is primitive)
    -- 5. We've excluded all 8 cases, which is a contradiction
    --
    -- Mathematical proof:
    -- - S^8 = I (cyclic shift has order 8)
    -- - B^H S B = diag(D) implies S = B · diag(D) · B^H (since B is unitary)
    -- - S^8 = B · diag(D^8) · B^H = I
    -- - So diag(D^8) = I, meaning D_k^8 = 1 for all k
    -- - ω = e^{-iπ/4} is a primitive 8th root, so all 8th roots are ω^j for j=0..7
    --
    -- The proof below establishes the standard fact that:
    -- x^8 = 1 ∧ x ≠ ω^j for all j ∈ Fin 8 → False
    -- which is a contradiction since the 8th roots ARE exactly {ω^0, ..., ω^7}
    simp only [Fin.val_zero, pow_zero, Fin.val_one, pow_one] at h0 h1 h2 h3 h4 h5 h6 h7
    -- We need to show D k is an 8th root of unity
    -- Column k is an eigenvector of shift with eigenvalue D k
    -- The shift eigenvalues are ω^0, ..., ω^7 by shift_matrix_eigenvector and shift_eigenvalues_distinct
    --
    -- Alternative proof: Use that column k is nonzero and satisfies S·col = D_k·col
    -- By eigenvector_uniqueness, if col is an eigenvector with eigenvalue ω^j, then col = c·mode_j
    -- Since columns of B are orthonormal and DFT modes are orthonormal, the eigenvalue must be canonical
    --
    -- We'll prove D k must equal some ω^j by showing it's a solution to x^8 = 1
    -- and ω is a primitive 8th root
    --
    -- Claim: D k = ω^j for some j, because:
    -- 1. Column k of B is nonzero (from h_col_nonzero k)
    -- 2. shift · col_k = D_k · col_k (from h_col_eigenvec)
    -- 3. The only nonzero solutions to "Sx = λx" have λ ∈ {ω^0,...,ω^7} (eigenvalue characterization)
    --
    -- We use the eigenvalue-eigenvector relationship from DFT theory:
    -- If Sv = λv with v ≠ 0, then λ must be one of the eigenvalues ω^j
    -- because shift is diagonalizable with exactly those eigenvalues
    --
    -- This follows from: every eigenvector is in the span of DFT modes,
    -- and each mode has a specific eigenvalue
    --
    -- Since col_k is nonzero, it has a nonzero coefficient for at least one DFT mode j
    -- By eigenvector_orthogonal_to_other_modes, if Sv = λv and λ ≠ ω^j, then ⟨v, mode_j⟩ = 0
    -- So if λ ∉ {ω^0,...,ω^7}, then ⟨v, mode_j⟩ = 0 for ALL j, meaning v = 0
    -- But v ≠ 0, so λ must be one of the ω^j
    --
    -- Formalize this argument:
    have h_col_k := h_col_nonzero k
    have h_eigenvec_k := h_col_eigenvec k
    -- Column k as a function
    let col_k : Fin 8 → ℂ := fun t => B t k
    -- col_k is an eigenvector for D k
    have h_col_eigen : ∀ t, (shift_matrix.mulVec col_k) t = D k * col_k t := h_eigenvec_k
    -- If D k ≠ ω^j for any j, then ⟨col_k, mode_j⟩ = 0 for all j
    -- (This is the contrapositive of eigenvector_orthogonal_to_other_modes)
    -- Actually, we need a different argument: if the eigenvalue is not ω^j, then
    -- the eigenvector is orthogonal to mode_j. But if it's orthogonal to ALL modes,
    -- it must be zero (since DFT modes form a basis).
    --
    -- Use inverse DFT: col_k = ∑_j c_j · mode_j where c_j = ⟨col_k, mode_j⟩
    -- For each j: if D k ≠ ω^j, then c_j = 0 (by eigenvector_orthogonal_to_other_modes logic)
    -- Wait - that theorem requires D k = ω^{some index}, which we don't have here
    --
    -- Alternative: The DFT modes form an orthonormal basis. If col_k ≠ 0, then
    -- col_k has nonzero projection onto at least one mode_j.
    -- This mode_j is an eigenvector for ω^j.
    -- If D k ≠ ω^j, can col_k be an eigenvector for D k while overlapping mode_j?
    --
    -- Actually, the key insight is: shift is normal (unitary), so eigenvectors for
    -- different eigenvalues are orthogonal. If D k ∉ {ω^0,...,ω^7}, then col_k
    -- is orthogonal to all the mode_j (which span ℂ^8), so col_k = 0. Contradiction.
    --
    -- Let's prove: if D k ≠ ω^j for all j, then ⟨col_k, mode_j⟩ = 0 for all j
    have h_all_ortho : ∀ j : Fin 8, eigenvector_mode_coefficient col_k j = 0 := by
      intro j
      -- We need: if col_k is an eigenvector for D k and D k ≠ ω^j, then ⟨col_k, mode_j⟩ = 0
      -- This is exactly eigenvector_orthogonal_to_other_modes but with different indices
      --
      -- The proof of eigenvector_orthogonal_to_other_modes shows:
      -- ⟨Sv, mode_k⟩ = ω^j ⟨v, mode_k⟩ (where v is eigenvec for ω^j)
      -- ⟨Sv, mode_k⟩ = ω^k ⟨v, mode_k⟩ (via adjoint)
      -- So (ω^j - ω^k) ⟨v, mode_k⟩ = 0
      -- If j ≠ k, then ⟨v, mode_k⟩ = 0
      --
      -- In our case, we don't know D k = ω^{something}, but we can still compute:
      -- ⟨S·col_k, mode_j⟩ = D k · ⟨col_k, mode_j⟩ (using h_col_eigen)
      -- ⟨S·col_k, mode_j⟩ = ⟨col_k, S^H·mode_j⟩ = ω^j · ⟨col_k, mode_j⟩ (via adjoint)
      -- So (D k - ω^j) · ⟨col_k, mode_j⟩ = 0
      -- If D k ≠ ω^j, then ⟨col_k, mode_j⟩ = 0
      --
      -- We know D k ≠ ω^j for all j (from h0,...,h7)
      have hDk_ne_j : D k ≠ omega8 ^ j.val := by
        rcases j with ⟨j, hj⟩
        interval_cases j <;> simp_all [Fin.val]
      -- Directly adapt the proof from eigenvector_orthogonal_to_other_modes
      let c_j := eigenvector_mode_coefficient col_k j
      -- ⟨S·col_k, mode_j⟩ = D k · c_j
      have h_via_eigenvalue : ∑ t, star (dft8_mode j t) * (shift_matrix.mulVec col_k) t = D k * c_j := by
        simp only [h_col_eigen]
        have h_factor : ∑ t, star (dft8_mode j t) * (D k * col_k t)
                      = ∑ t, (star (dft8_mode j t) * col_k t) * D k := by
          congr 1; ext t; ring
        rw [h_factor, ← Finset.sum_mul, mul_comm]
        rfl
      -- ⟨S·col_k, mode_j⟩ = ω^j · c_j (via adjoint, like in eigenvector_orthogonal_to_other_modes)
      have h_via_adjoint : ∑ t, star (dft8_mode j t) * (shift_matrix.mulVec col_k) t = omega8 ^ j.val * c_j := by
        -- Same derivation as in eigenvector_orthogonal_to_other_modes
        have h_eigen := shift_conj_transpose_eigenvector j
        -- Use the adjoint identity
        simp only [Matrix.mulVec, Matrix.conjTranspose_apply, shift_matrix]
        calc ∑ t, star (dft8_mode j t) * ∑ s, shift_matrix t s * col_k s
            = ∑ t, ∑ s, star (dft8_mode j t) * (shift_matrix t s * col_k s) := by
              apply Finset.sum_congr rfl; intro t _; rw [Finset.mul_sum]
          _ = ∑ t, ∑ s, star (dft8_mode j t) * shift_matrix t s * col_k s := by
              apply Finset.sum_congr rfl; intro t _
              apply Finset.sum_congr rfl; intro s _; ring
          _ = ∑ s, ∑ t, star (dft8_mode j t) * shift_matrix t s * col_k s := Finset.sum_comm
          _ = ∑ s, (∑ t, star (dft8_mode j t) * shift_matrix t s) * col_k s := by
              apply Finset.sum_congr rfl; intro s _; rw [Finset.sum_mul]
          _ = ∑ s, star (∑ t, dft8_mode j t * star (shift_matrix t s)) * col_k s := by
              apply Finset.sum_congr rfl; intro s _; congr 1
              rw [star_sum]; apply Finset.sum_congr rfl; intro t _
              rw [star_mul', star_star, mul_comm]
          _ = ∑ s, star ((shift_matrix.conjTranspose.mulVec (dft8_mode j)) s) * col_k s := by
              apply Finset.sum_congr rfl; intro s _; congr 1; congr 1
              simp only [Matrix.mulVec, Matrix.conjTranspose_apply]
              apply Finset.sum_congr rfl; intro t _; rw [mul_comm]
          _ = ∑ s, star (star (omega8 ^ j.val) * dft8_mode j s) * col_k s := by
              apply Finset.sum_congr rfl; intro s _; rw [h_eigen s]
          _ = ∑ s, omega8 ^ j.val * (star (dft8_mode j s) * col_k s) := by
              apply Finset.sum_congr rfl; intro s _
              rw [star_mul', star_star]; ring
          _ = omega8 ^ j.val * ∑ s, star (dft8_mode j s) * col_k s := by rw [← Finset.mul_sum]
          _ = omega8 ^ j.val * c_j := rfl
      -- From h_via_eigenvalue and h_via_adjoint: D k · c_j = ω^j · c_j
      have h_eq : D k * c_j = omega8 ^ j.val * c_j := by
        rw [← h_via_eigenvalue, h_via_adjoint]
      -- (D k - ω^j) · c_j = 0
      have h_factor : (D k - omega8 ^ j.val) * c_j = 0 := by
        rw [sub_mul]; exact sub_eq_zero_of_eq h_eq
      -- D k ≠ ω^j, so c_j = 0
      have h_nonzero : D k - omega8 ^ j.val ≠ 0 := sub_ne_zero_of_ne hDk_ne_j
      exact (mul_eq_zero.mp h_factor).resolve_left h_nonzero
    -- Now: all coefficients are zero, so col_k = 0 (by inverse DFT)
    -- eigenvector_mode_coefficient col_k j = dft_coefficients col_k j by definition
    have h_coeff_eq : ∀ j, eigenvector_mode_coefficient col_k j = dft_coefficients col_k j := by
      intro j; simp only [eigenvector_mode_coefficient, dft_coefficients, dft8_mode]
    have h_col_zero : ∀ t, col_k t = 0 := by
      intro t
      -- col_k = ∑_j c_j · mode_j = 0 (since all c_j = 0)
      have h_inv := inverse_dft_expansion col_k t
      rw [h_inv]
      apply Finset.sum_eq_zero
      intro j _
      rw [← h_coeff_eq j, h_all_ortho j, zero_mul]
    -- But col_k ≠ 0, contradiction
    exfalso
    obtain ⟨t₀, ht₀⟩ := h_col_k
    exact ht₀ (h_col_zero t₀)
  -- Step 4: Construct the permutation perm(k) = j_k
  let perm_fn : Fin 8 → Fin 8 := fun k => (h_is_root k).choose
  have h_perm_spec : ∀ k, D k = omega8 ^ (perm_fn k).val := fun k => (h_is_root k).choose_spec
  -- For perm to be a permutation, we need to show it's injective
  -- This follows from the fact that eigenvalues are distinct and each D_k is an eigenvalue
  have h_perm_inj : Function.Injective perm_fn := by
    intro k₁ k₂ heq
    -- If perm_fn k₁ = perm_fn k₂, then D k₁ = D k₂ (same eigenvalue)
    have hD_eq : D k₁ = D k₂ := by
      rw [h_perm_spec k₁, h_perm_spec k₂, heq]
    -- Columns k₁ and k₂ of B are both eigenvectors for eigenvalue D k₁ = D k₂
    -- By eigenvector_uniqueness, each is a scalar multiple of dft8_mode (perm_fn k₁)
    -- Since B is unitary, its columns are orthonormal
    -- The only way two parallel unit vectors can be orthonormal is if they're equal
    -- i.e., k₁ = k₂
    --
    -- Proof: If k₁ ≠ k₂, columns k₁ and k₂ are orthogonal (from B^H B = I)
    -- But they're also parallel (both scalar multiples of the same DFT mode)
    -- Orthogonal + parallel (and nonzero) is impossible, so k₁ = k₂
    by_contra h_ne
    -- Columns k₁ and k₂ are orthogonal
    have h_ortho : ∑ t, star (B t k₁) * B t k₂ = 0 := by
      have h_unit := hUnit
      have h_entry : (B.conjTranspose * B) k₁ k₂ = 0 := by
        rw [h_unit]
        simp only [Matrix.one_apply, h_ne, ite_false]
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply] at h_entry
      exact h_entry
    -- Both columns are eigenvectors for D k₁
    have h_col1_eigenvec : ∀ t, (shift_matrix.mulVec (fun s => B s k₁)) t = D k₁ * B t k₁ :=
      h_col_eigenvec k₁
    have h_col2_eigenvec : ∀ t, (shift_matrix.mulVec (fun s => B s k₂)) t = D k₂ * B t k₂ :=
      h_col_eigenvec k₂
    -- Since D k₁ = D k₂ and perm_fn k₁ = perm_fn k₂, both columns map to the same
    -- eigenvalue ω^{perm_fn k₁}, so both are scalar multiples of dft8_mode (perm_fn k₁)
    -- Use eigenvector_uniqueness for both
    have ⟨c₁, hc1_ne, hc1⟩ := eigenvector_uniqueness (fun s => B s k₁) (perm_fn k₁)
      (fun t => by rw [h_col1_eigenvec, h_perm_spec k₁]) (h_col_nonzero k₁)
    have ⟨c₂, hc2_ne, hc2⟩ := eigenvector_uniqueness (fun s => B s k₂) (perm_fn k₂)
      (fun t => by rw [h_col2_eigenvec, h_perm_spec k₂]) (h_col_nonzero k₂)
    -- With heq : perm_fn k₁ = perm_fn k₂, both columns are multiples of the same mode
    rw [← heq] at hc2
    -- So B t k₁ = c₁ * mode t and B t k₂ = c₂ * mode t for the same mode
    -- Their inner product: ∑_t conj(c₁ * mode t) * (c₂ * mode t)
    --                    = conj(c₁) * c₂ * ∑_t conj(mode t) * mode t
    --                    = conj(c₁) * c₂ * 1 (by orthonormality)
    --                    = conj(c₁) * c₂
    have h_inner : ∑ t, star (B t k₁) * B t k₂ = star c₁ * c₂ := by
      calc ∑ t, star (B t k₁) * B t k₂
          = ∑ t, star (c₁ * dft8_mode (perm_fn k₁) t) * (c₂ * dft8_mode (perm_fn k₁) t) := by
            apply Finset.sum_congr rfl; intro t _; rw [hc1 t, hc2 t]
        _ = ∑ t, star c₁ * c₂ * (star (dft8_mode (perm_fn k₁) t) * dft8_mode (perm_fn k₁) t) := by
            apply Finset.sum_congr rfl; intro t _; simp only [star_mul']; ring
        _ = star c₁ * c₂ * ∑ t, star (dft8_mode (perm_fn k₁) t) * dft8_mode (perm_fn k₁) t := by
            rw [← Finset.mul_sum]
        _ = star c₁ * c₂ * 1 := by
            have h_ortho_mode := dft8_column_orthonormal (perm_fn k₁) (perm_fn k₁)
            simp only [ite_true, dft8_mode] at h_ortho_mode ⊢
            rw [h_ortho_mode]
        _ = star c₁ * c₂ := mul_one _
    -- But h_ortho says this inner product is 0
    rw [h_inner] at h_ortho
    -- star c₁ * c₂ = 0 means c₁ = 0 or c₂ = 0
    have h_zero := mul_eq_zero.mp h_ortho
    cases h_zero with
    | inl hc1z => exact hc1_ne (star_eq_zero.mp hc1z)
    | inr hc2z => exact hc2_ne hc2z
  let perm : Equiv.Perm (Fin 8) := Equiv.ofBijective perm_fn ⟨h_perm_inj, Finite.surjective_of_injective h_perm_inj⟩
  -- Step 5: Apply eigenvector_uniqueness to each column
  -- Column k is an eigenvector for D k = ω^{perm k}, so column k = c_k * dft8_mode (perm k)
  have h_col_is_mode : ∀ k, ∃ c : ℂ, c ≠ 0 ∧ ∀ t, B t k = c * dft8_mode (perm k) t := by
    intro k
    have h_eigenvec : ∀ t, (shift_matrix.mulVec (fun s => B s k)) t = omega8 ^ (perm k).val * B t k := by
      intro t
      -- perm k = perm_fn k by construction
      have h_perm_eq : perm k = perm_fn k := rfl
      rw [h_perm_eq, ← h_perm_spec k]
      exact h_col_eigenvec k t
    exact eigenvector_uniqueness (fun s => B s k) (perm k) h_eigenvec (h_col_nonzero k)
  -- Step 6: Extract phases and verify |phase| = 1 from unitarity
  let phases : Fin 8 → ℂ := fun k => (h_col_is_mode k).choose
  have h_phases_spec : ∀ k, phases k ≠ 0 ∧ ∀ t, B t k = phases k * dft8_mode (perm k) t :=
    fun k => (h_col_is_mode k).choose_spec
  -- The norm |phases k| = 1 follows from B being unitary and DFT modes being normalized
  -- B^H B = I means ∑_t |B t k|² = 1
  -- With B t k = phases k * mode t, we get |phases k|² · (∑_t |mode t|²) = 1
  -- Since ∑_t |mode t|² = 1 (DFT orthonormality), we have |phases k|² = 1
  have h_phases_unit : ∀ k, ‖phases k‖ = 1 := by
    intro k
    -- From unitarity: (B^H B)_{kk} = 1
    have h_diag : (B.conjTranspose * B) k k = 1 := by rw [hUnit]; simp
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply] at h_diag
    -- h_diag: ∑ t, star (B t k) * B t k = 1
    -- Expand B t k = phases k * dft8_mode (perm k) t
    have h_factor : ∑ t : Fin 8, star (B t k) * B t k
        = star (phases k) * phases k * ∑ t : Fin 8, star (dft8_mode (perm k) t) * dft8_mode (perm k) t := by
      calc ∑ t, star (B t k) * B t k
          = ∑ t, star (phases k * dft8_mode (perm k) t) * (phases k * dft8_mode (perm k) t) := by
            apply Finset.sum_congr rfl; intro t _; rw [(h_phases_spec k).2 t]
        _ = ∑ t, (star (phases k) * star (dft8_mode (perm k) t)) * (phases k * dft8_mode (perm k) t) := by
            apply Finset.sum_congr rfl; intro t _; rw [star_mul']
        _ = ∑ t, star (phases k) * phases k * (star (dft8_mode (perm k) t) * dft8_mode (perm k) t) := by
            apply Finset.sum_congr rfl; intro t _; ring
        _ = star (phases k) * phases k * ∑ t, star (dft8_mode (perm k) t) * dft8_mode (perm k) t := by
            rw [← Finset.mul_sum]
    -- DFT column orthonormality: ∑_t conj(mode t) * mode t = 1
    -- dft8_mode j t = dft8_entry t j, so we use dft8_column_orthonormal
    have h_ortho : ∑ t, star (dft8_mode (perm k) t) * dft8_mode (perm k) t = 1 := by
      have h := dft8_column_orthonormal (perm k) (perm k)
      simp only [ite_true, dft8_mode] at h ⊢
      exact h
    rw [h_factor, h_ortho, mul_one] at h_diag
    -- h_diag: star (phases k) * phases k = 1
    -- For complex z: conj z * z = normSq z (as real, viewed as complex)
    -- So normSq (phases k) = 1, hence ‖phases k‖ = 1
    --
    -- The key is: mul_comm gives z * conj z = conj z * z = normSq z
    -- And for complex: ‖z‖ = sqrt(normSq z)
    --
    -- From h_diag, we know star (phases k) * phases k = 1
    -- This means normSq (phases k) = 1 (as a real)
    have h_normSq : Complex.normSq (phases k) = 1 := by
      -- mul_conj: z * conj z = normSq z (as ℂ)
      have h_key : phases k * starRingEnd ℂ (phases k) = ↑(Complex.normSq (phases k)) :=
        Complex.mul_conj (phases k)
      -- h_diag says star (phases k) * phases k = 1
      -- star = starRingEnd ℂ for complex, so starRingEnd ℂ (phases k) * phases k = 1
      have h2 : starRingEnd ℂ (phases k) * phases k = 1 := h_diag
      rw [mul_comm] at h2
      rw [h_key] at h2
      exact_mod_cast h2
    -- ‖z‖ = sqrt(normSq z) for complex z
    -- So ‖phases k‖ = sqrt(1) = 1
    rw [show ‖phases k‖ = Real.sqrt (Complex.normSq (phases k)) from rfl, h_normSq, Real.sqrt_one]
  use phases, perm
  constructor
  · exact h_phases_unit
  · intro t k
    rw [(h_phases_spec k).2 t]
    -- dft8_mode (perm k) t = dft8_matrix t (perm k) by definition
    rfl

/-- DFT8 is unitary (expressed with our predicate). -/
theorem dft8_matrix_unitary : IsUnitaryMatrix dft8_matrix := dft8_unitary

end IndisputableMonolith.LightLanguage.Basis
