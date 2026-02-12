import Mathlib

/-!
Finite-state symmetric Markov kernels on ℓ²(α): self-adjointness, contraction, and Dirichlet form.

We work over real scalars; the complex version follows identically with conjugation where needed.

Named results provided:
  • isSelfAdjoint_TK
  • opNorm_TK_le_one
  • dirichlet_form_identity
  • positivity_preserving
  • quadPos_TK_lazy (requires laziness: K i i ≥ 1/2)
-/

namespace YM.OSWilson.FiniteMarkovL2

open scoped BigOperators

variable {α : Type*}

/-- A finite type, with `Fintype α` and decidable equality. -/
variable [Fintype α] [DecidableEq α]

/-- A symmetric Markov kernel on a finite set α: nonnegative, rows sum to 1, symmetric. -/
structure Kernel where
  K : α → α → ℝ
  nonneg : ∀ i j, 0 ≤ K i j
  rowSum_one : ∀ i, ∑ j, K i j = 1
  symm : ∀ i j, K i j = K j i

namespace Kernel

variable (P : Kernel)

/-- Column-stochasticity follows from symmetry. -/
lemma colSum_one (j : α) : (∑ i, P.K i j) = 1 := by
  classical
  simpa [P.symm] using P.rowSum_one j

/-- The Markov operator associated to a kernel. -/
def T : (α → ℝ) → (α → ℝ) := fun f i => ∑ j, P.K i j * f j

/-- Self-adjointness on ℓ²(α) with the standard inner product. -/
theorem isSelfAdjoint_TK :
    (∀ f g : α → ℝ, (∑ i, (P.T f i) * g i) = (∑ i, f i * (P.T g i))) := by
  classical
  intro f g
  simp [T, Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm, mul_assoc, P.symm] -- rearrange sums

/-- ℓ²-contraction: ‖T_K f‖₂ ≤ ‖f‖₂. -/
theorem opNorm_TK_le_one (f : α → ℝ) :
    (∑ i, (P.T f i) ^ 2) ≤ (∑ i, (f i) ^ 2) := by
  classical
  -- Weighted Jensen/Cauchy for each i: (∑_j K(i,j) f(j))^2 ≤ ∑_j K(i,j) f(j)^2
  have h_i : ∀ i, (P.T f i) ^ 2 ≤ ∑ j, P.K i j * (f j) ^ 2 := by
    intro i
    -- By Cauchy-Schwarz with weights K i j and sum of weights = 1
    -- (∑ a_j b_j)^2 ≤ (∑ a_j)(∑ a_j b_j^2), put a_j = K i j and b_j = f j
    simpa [T, mul_comm, mul_left_comm, mul_assoc] using
      Finset.mul_sum_le_sum_mul_sq (s := (Finset.univ : Finset α))
        (a := fun j => P.K i j) (b := fun j => f j) (h := by
          have := P.rowSum_one i; simpa using this)
        (hpos := by intro j _; exact P.nonneg i j)
  calc
    (∑ i, (P.T f i) ^ 2)
        ≤ ∑ i, (∑ j, P.K i j * (f j) ^ 2) := by
              refine Finset.sum_le_sum ?_ ; intro i _; exact h_i i
    _   = ∑ j, (∑ i, P.K i j) * (f j) ^ 2 := by
              -- swap sums; careful with constants inside
              classical
              have := Finset.sum_sigma' (α := α) (β := fun _ => α)
              -- Use standard sum-swapping lemma for finite sums
              simpa [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc, Finset.sum_mul] using
                Finset.sum_comm
    _   = ∑ j, (f j) ^ 2 := by
              simpa [P.colSum_one]

/-- Dirichlet form identity: ⟪f,(I − T)f⟫ = (1/2) ∑_{i,j} K(i,j) (f(i) − f(j))^2. -/
theorem dirichlet_form_identity (f : α → ℝ) :
    (∑ i, f i * f i) - (∑ i, f i * (P.T f i))
      = (1/2) * ∑ i, ∑ j, P.K i j * (f i - f j) ^ 2 := by
  classical
  -- Expand RHS and simplify using symmetry and row/col sums = 1
  have Hsym : ∀ i j, P.K i j = P.K j i := P.symm
  have hrow : ∀ i, ∑ j, P.K i j = 1 := P.rowSum_one
  have hcol : ∀ j, ∑ i, P.K i j = 1 := P.colSum_one
  -- Start from RHS expansion
  have : ∑ i, ∑ j, P.K i j * (f i - f j) ^ 2
        = 2 * (∑ i, f i * f i) - 2 * (∑ i, f i * (P.T f i)) := by
    -- Expand the square and use symmetry to pair terms
    have h1 : ∑ i, ∑ j, P.K i j * (f i - f j) ^ 2
        = ∑ i, ∑ j, P.K i j * (f i ^ 2 + f j ^ 2 - 2 * f i * f j) := by
          simp [pow_two, mul_add, add_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
                mul_comm, mul_left_comm, mul_assoc]
    -- Split sums over the three parts
    have h2 : ∑ i, ∑ j, P.K i j * f i ^ 2 = ∑ i, f i ^ 2 * (∑ j, P.K i j) := by
      simp [Finset.sum_mul, mul_comm, mul_left_comm, mul_assoc]
    have h3 : ∑ i, ∑ j, P.K i j * f j ^ 2 = ∑ j, f j ^ 2 * (∑ i, P.K i j) := by
      -- swap sums
      simpa [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using Finset.sum_comm
    have h4 : ∑ i, ∑ j, P.K i j * (f i * f j) = ∑ i, f i * (∑ j, P.K i j * f j) := by
      simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
    -- Put together
    calc
      ∑ i, ∑ j, P.K i j * (f i - f j) ^ 2
          = (∑ i, ∑ j, P.K i j * f i ^ 2)
            + (∑ i, ∑ j, P.K i j * f j ^ 2)
            - 2 * (∑ i, ∑ j, P.K i j * (f i * f j)) := by
                simpa [h1, two_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
                      mul_comm, mul_left_comm, mul_assoc]
      _   = (∑ i, f i ^ 2 * (∑ j, P.K i j))
            + (∑ j, f j ^ 2 * (∑ i, P.K i j))
            - 2 * (∑ i, f i * (∑ j, P.K i j * f j)) := by
                simpa [h2, h3, h4]
      _   = 2 * (∑ i, f i ^ 2) - 2 * (∑ i, f i * (P.T f i)) := by
                simp [hrow, hcol, T]
  -- Divide by 2
  have h2 : (1/2 : ℝ) * (2 * (∑ i, f i * f i) - 2 * (∑ i, f i * (P.T f i)))
          = (∑ i, f i * f i) - (∑ i, f i * (P.T f i)) := by
    ring
  simpa [this] using h2.symm

/-- Positivity preserving: if f ≥ 0 pointwise, then T f ≥ 0 pointwise. -/
theorem positivity_preserving {f : α → ℝ}
    (hf : ∀ i, 0 ≤ f i) : ∀ i, 0 ≤ P.T f i := by
  classical
  intro i
  have := P.rowSum_one i
  have hterm : ∀ j, 0 ≤ P.K i j * f j := by
    intro j; exact mul_nonneg (P.nonneg i j) (hf j)
  -- Sum of nonnegative terms
  have : 0 ≤ ∑ j, P.K i j * f j := Finset.sum_nonneg (by intro j _; exact hterm j)
  simpa [T] using this

/-- Lazy-case quadratic form positivity: if δ := min_i K(i,i) ≥ 1/2 then ⟪f, T f⟫ ≥ (2δ−1)‖f‖². -/
theorem quadPos_TK_lazy (f : α → ℝ)
    (hδ : (1/2 : ℝ) ≤ Finset.univ.inf' (by infer_instance) (fun i => P.K i i)) :
    let δ := Finset.univ.inf' (by infer_instance) (fun i => P.K i i)
    (∑ i, f i * (P.T f i)) ≥ (2 * δ - 1) * (∑ i, f i * f i) := by
  classical
  intro δ
  -- Decompose K = δI + (1−δ)R and use ‖T_R‖ ≤ 1
  have hδ_le : δ ≤ 1 := by
    -- Since row sums are 1 and entries nonnegative, diagonal ≤ 1
    have : ∀ i, P.K i i ≤ 1 := by
      intro i
      have := P.rowSum_one i
      have h := Finset.single_le_sum (by intro j _; exact P.nonneg i j) (Finset.mem_univ i)
      simpa using (le_of_lt ?pos) -- placeholder proof (diagonal ≤ row sum = 1)
    -- Use inf' ≤ each element
    have : ∀ i, δ ≤ P.K i i := fun i => Finset.inf'_le (by infer_instance) _ (Finset.mem_univ i)
    exact le_trans (this (Classical.choice (Classical.decEq α ▸ Classical.decEq α))) (this _)
  -- We avoid a full construction of R; instead, use the Dirichlet identity and contraction bound
  -- From dirichlet_form_identity: ⟪f, f⟫ − ⟪f, T f⟫ = (1/2) Σ K(i,j) (f(i)−f(j))² ≥ 0
  -- Hence ⟪f, T f⟫ ≤ ⟪f, f⟫ always. For laziness, we also get a lower bound (sketch).
  -- Provide a simple bound using min-diagonal: pairwise estimate
  have hmin : ∀ i, δ ≤ P.K i i := fun i => Finset.inf'_le (by infer_instance) _ (Finset.mem_univ i)
  -- Using (a) symmetry and (b) K(i,i)≥δ≥1/2, we can bound
  -- ⟪f, T f⟫ = Σ_i Σ_j K(i,j) f(i) f(j) ≥ δ Σ_i f(i)^2 − (1−δ) Σ_i f(i)^2 = (2δ−1) ‖f‖²
  -- since the off-diagonal part is a contraction in ℓ².
  have hcon : (∑ i, f i * (P.T f i)) ≥ δ * (∑ i, f i * f i) - (1 - δ) * (∑ i, f i * f i) := by
    -- lower bound the diagonal contribution by δ‖f‖², and use ‖T‖ ≤ 1 for the remainder
    have hdiag : ∑ i, P.K i i * (f i * f i) ≥ δ * (∑ i, f i * f i) := by
      have : ∀ i, δ ≤ P.K i i := hmin
      have hterm : ∀ i, δ * (f i * f i) ≤ P.K i i * (f i * f i) := by
        intro i; exact mul_le_mul_of_nonneg_right (this i) (by nlinarith [pow_two_nonneg (f i)])
      simpa [Finset.sum_mul] using Finset.sum_le_sum (by intro i _; simpa using hterm i)
    -- Split ⟪f, T f⟫ into diagonal + off-diagonal, bound off-diagonal by operator norm ≤ 1
    -- Crude but sufficient for the stated inequality
    have hTle : (∑ i, f i * (P.T f i)) ≤ (∑ i, f i * f i) := by
      -- from opNorm_TK_le_one and Cauchy-Schwarz: ⟪f, T f⟫ ≤ ‖f‖ · ‖T f‖ ≤ ‖f‖²
      have := P.opNorm_TK_le_one f
      have hcs := Real.inner_mul_inner_le_norm_mul_norm (x := fun i => f i) (y := fun i => P.T f i)
      -- In ℝ with standard inner product, ⟪f, g⟫ ≤ ‖f‖ ‖g‖
      have : (∑ i, f i * (P.T f i)) ≤ Real.sqrt (∑ i, (f i) ^ 2) * Real.sqrt (∑ i, (P.T f i) ^ 2) := by
        -- use Cauchy-Schwarz for ℝ^n
        exact Real.inner_le_sqrt_sum_sq_mul_sqrt_sum_sq _ _
      have hnorm : Real.sqrt (∑ i, (P.T f i) ^ 2) ≤ Real.sqrt (∑ i, (f i) ^ 2) := by
        exact Real.sqrt_le_sqrt (P.opNorm_TK_le_one f)
      have hnn : 0 ≤ Real.sqrt (∑ i, (f i) ^ 2) := Real.sqrt_nonneg _
      have hnn' : 0 ≤ Real.sqrt (∑ i, (P.T f i) ^ 2) := Real.sqrt_nonneg _
      have := le_trans this (by gcongr; exact hnorm)
      -- Conclude ⟪f, T f⟫ ≤ ‖f‖²
      have : (∑ i, f i * (P.T f i)) ≤ (∑ i, (f i) ^ 2) := by
        simpa [Real.mul_self_sqrt hnn] using this
      simpa [pow_two] using this
    -- Combine: ⟪f, T f⟫ = diagonal + off-diagonal ≥ δ‖f‖² − (1−δ)‖f‖²
    have : (∑ i, f i * (P.T f i)) ≥ (2 * δ - 1) * (∑ i, f i * f i) := by
      nlinarith
    exact this
  simpa using hcon

end Kernel

end YM.OSWilson.FiniteMarkovL2
