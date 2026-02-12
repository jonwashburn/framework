import Hodge.Kahler.Manifolds
import Hodge.Kahler.TypeDecomposition
import Hodge.Kahler.Cone
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Basic
import Hodge.Analytic.Norms
import Mathlib.Algebra.Order.Field.Basic

/-!
# Track C.4: Signed Decomposition

This file proves the signed decomposition theorem for rational Hodge classes.
-/

noncomputable section

open Classical Set Filter Hodge

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
  [Nonempty X]

/-! ## Helper lemmas for rationality -/

/-- ω^p is a rational class. -/
theorem omega_pow_is_rational_SD (p : ℕ) : isRationalClass ⟦kahlerPow (n := n) (X := X) p, omega_pow_IsFormClosed (n := n) (X := X) p⟧ :=
  omega_pow_is_rational_TD p

/-! ## Signed Decomposition -/

/-- **Lemma: Signed Decomposition** (Lemma 8.7)
    Let γ be a rational Hodge class. Then γ = γ⁺ - γ⁻ where γ⁺ and γ⁻ are
    cone-positive rational Hodge classes. -/
structure SignedDecomposition {p : ℕ} (γ : SmoothForm n X (2 * p)) (h_closed : IsFormClosed γ) where
  γplus : SmoothForm n X (2 * p)
  γminus : SmoothForm n X (2 * p)
  N : ℚ
  h_plus_closed : IsFormClosed γplus
  h_minus_closed : IsFormClosed γminus
  h_eq : γ = γplus - γminus
  h_plus_cone : isConePositive γplus
  h_minus_cone : isConePositive γminus
  h_plus_rat : isRationalClass ⟦γplus, h_plus_closed⟧
  h_minus_rat : isRationalClass ⟦γminus, h_minus_closed⟧
  h_N_pos : N > 0
  h_gamma_minus : γminus = (N : ℝ) • kahlerPow p

/-- **Definition: Signed Decomposition** (Lemma 8.7)
    Given a representative form γ of a rational Hodge class, there exists a signed
    decomposition of γ. This is Lemma 8.7 in the manuscript.

    **Proof Construction:**
    1. Use `shift_makes_conePositive_rat` to find N : ℚ with N > 0 such that
       γ + N·ω^p is cone-positive
    2. Set γ⁺ := γ + N·ω^p (cone-positive by construction)
    3. Set γ⁻ := N·ω^p (cone-positive since N > 0 and ω^p is in cone interior)
    4. Then γ = γ⁺ - γ⁻
    5. Both γ⁺ and γ⁻ are closed (γ is closed, ω^p is closed)
    6. Both represent rational classes (γ is rational, ω^p is rational, rational + rational = rational)

    Reference: [P. Griffiths and J. Harris, "Principles of Algebraic Geometry",
    Wiley, 1978, Chapter 1, Section 3]. -/
def signed_decomposition {p : ℕ} (γ : SmoothForm n X (2 * p)) (h_closed : IsFormClosed γ)
    (_h_hodge : isPPForm' n X p γ) (h_rational : isRationalClass ⟦γ, h_closed⟧) :
    SignedDecomposition γ h_closed :=
  -- Step 1: Find N > 0 such that γ + N·ω^p is cone-positive
  let h_exists := shift_makes_conePositive_rat p γ
  let N := Classical.choose h_exists
  let hN_spec := Classical.choose_spec h_exists
  let hN_pos : N > 0 := hN_spec.1
  let h_cone_plus : isConePositive (γ + (N : ℝ) • kahlerPow p) := hN_spec.2

  -- Step 2: Define γ⁺ and γ⁻
  let γplus := γ + (N : ℝ) • kahlerPow p
  let γminus := (N : ℝ) • kahlerPow p

  -- Step 3: Prove closedness
  let h_omega_closed : IsFormClosed (kahlerPow (n := n) (X := X) p) := omega_pow_IsFormClosed p
  let h_gamma_minus_closed : IsFormClosed γminus := isFormClosed_smul_real h_omega_closed
  let h_gamma_plus_closed : IsFormClosed γplus := isFormClosed_add h_closed h_gamma_minus_closed

  -- Step 4: Prove γ⁻ is cone-positive (positive multiple of ω^p)
  let h_minus_cone : isConePositive γminus := kahlerPow_smul_isConePositive p (N : ℝ) (by exact mod_cast hN_pos)

  -- Step 5: Prove rationality
  let h_omega_rat : isRationalClass ⟦kahlerPow (n := n) (X := X) p, h_omega_closed⟧ :=
    omega_pow_is_rational_TD p

  -- For γ⁻ = N·ω^p with N : ℚ, use rational scalar multiplication on a rational class
  let h_minus_rat : isRationalClass ⟦γminus, h_gamma_minus_closed⟧ :=
    -- The cohomology class equals N • [ω^p], which is rational
    let h_class_eq : ⟦γminus, h_gamma_minus_closed⟧ = (N : ℝ) • ⟦kahlerPow (n := n) (X := X) p, h_omega_closed⟧ :=
      by simpa using ofForm_smul_real (N : ℝ) (kahlerPow p) h_omega_closed
    -- Use compatibility: (N : ℝ) • c = N • c
    let h_smul_compat : N • ⟦kahlerPow (n := n) (X := X) p, h_omega_closed⟧ =
                         (N : ℝ) • ⟦kahlerPow (n := n) (X := X) p, h_omega_closed⟧ :=
      smul_rat_eq_smul_real N ⟦kahlerPow (n := n) (X := X) p, h_omega_closed⟧
    (h_class_eq.trans h_smul_compat.symm) ▸ isRationalClass_smul_rat N ⟦kahlerPow (n := n) (X := X) p, h_omega_closed⟧ h_omega_rat

  let h_plus_rat : isRationalClass ⟦γplus, h_gamma_plus_closed⟧ :=
    -- γ⁺ = γ + N·ω^p, use ofForm_add
    let h_class_eq : ⟦γplus, h_gamma_plus_closed⟧ = ⟦γ, h_closed⟧ + ⟦γminus, h_gamma_minus_closed⟧ :=
      by simpa using ofForm_add γ γminus h_closed h_gamma_minus_closed
    h_class_eq ▸ isRationalClass_add ⟦γ, h_closed⟧ ⟦γminus, h_gamma_minus_closed⟧ h_rational h_minus_rat

  -- Step 6: Build the structure
  {
    γplus := γplus
    γminus := γminus
    N := N
    h_plus_closed := h_gamma_plus_closed
    h_minus_closed := h_gamma_minus_closed
    h_eq := by
      -- γ = (γ + N•ω^p) - N•ω^p
      show γ = γplus - γminus
      simp only [γplus, γminus]
      -- Use: (γ + a) - a = γ
      ext x v
      simp only [SmoothForm.sub_apply, SmoothForm.add_apply, SmoothForm.smul_apply]
      simp only [add_sub_cancel_right]
    h_plus_cone := h_cone_plus
    h_minus_cone := h_minus_cone
    h_plus_rat := h_plus_rat
    h_minus_rat := h_minus_rat
    h_N_pos := hN_pos
    h_gamma_minus := rfl
  }

end
