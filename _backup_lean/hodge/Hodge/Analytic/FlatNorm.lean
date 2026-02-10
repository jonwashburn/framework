import Hodge.Analytic.Currents
import Hodge.Analytic.Norms
import Hodge.Cohomology.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Flat Norm on Currents

This file defines the flat norm on currents and proves its basic properties.
The flat norm is the natural metric for the space of integral currents.

## Main Definitions

* `flatNormDecompSet` - The set of valid decomposition costs for flat norm
* `flatNorm` - The flat norm of a current, defined as an infimum

## Main Results (Proven)

* `flatNorm_nonneg` - The flat norm is non-negative
* `flatNorm_zero` - The flat norm of zero is zero
* `flatNorm_le_mass` - The flat norm is bounded by the mass
* `flatNorm_boundary_le` - The flat norm of a boundary is bounded by mass

## References

* [H. Federer and W.H. Fleming, "Normal and integral currents", 1960]
-/

noncomputable section

open Classical Set Hodge
open scoped BigOperators

set_option autoImplicit false

variable {n : ℕ} {X : Type*}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
  [Nonempty X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-! ## Auxiliary Lemmas -/

/-- The boundary of the zero current is zero. -/
theorem Current.boundary_zero {k : ℕ} : Current.boundary (0 : Current n X (k + 1)) = 0 := by
  ext ω
  show (0 : Current n X (k + 1)).toFun (smoothExtDeriv ω) = (0 : Current n X k).toFun ω
  rw [Current.zero_toFun, Current.zero_toFun]

/-- Scalar multiplication of boundary. -/
theorem Current.boundary_smul {k : ℕ} (c : ℝ) (R : Current n X (k + 1)) :
    Current.boundary (c • R) = c • Current.boundary R := by
  -- boundary (c • R) = c • boundary R
  -- By extensionality: for all ω, (boundary (c • R)).toFun ω = (c • boundary R).toFun ω
  -- LHS = (c • R).toFun (dω) = c * R.toFun (dω)  [by defs of boundary, smul_curr]
  -- RHS = c * (boundary R).toFun ω = c * R.toFun (dω)  [by defs of smul_curr, boundary]
  rfl

/-! ## Flat Norm Definition -/

/-- The decomposition set for flat norm computation.
    A valid decomposition of T consists of currents (S, R) with T = S + ∂R,
    and the cost is M(S) + M(R). -/
def flatNormDecompSet {k : ℕ} (T : Current n X k) : Set ℝ :=
  { m : ℝ | ∃ (S : Current n X k) (R : Current n X (k + 1)),
    T = S + Current.boundary R ∧ m = Current.mass S + Current.mass R }

/-- The trivial decomposition T = T + ∂0 shows the decomposition set is nonempty. -/
theorem flatNormDecompSet_nonempty {k : ℕ} (T : Current n X k) :
    (flatNormDecompSet T).Nonempty := by
  use Current.mass T + Current.mass (0 : Current n X (k + 1))
  use T, 0
  refine ⟨?_, rfl⟩
  ext ω
  rw [Current.boundary_zero]
  show T.toFun ω = (T + (0 : Current n X k)).toFun ω
  rw [Current.add_zero]

/-- Every element of the decomposition set is non-negative. -/
theorem flatNormDecompSet_nonneg {k : ℕ} (T : Current n X k) :
    ∀ m ∈ flatNormDecompSet T, m ≥ 0 := by
  intro m ⟨S, R, _, hm⟩
  rw [hm]
  exact add_nonneg (Current.mass_nonneg S) (Current.mass_nonneg R)

/-- The decomposition set is bounded below by 0. -/
theorem flatNormDecompSet_bddBelow {k : ℕ} (T : Current n X k) :
    BddBelow (flatNormDecompSet T) := ⟨0, fun _ hm => flatNormDecompSet_nonneg T _ hm⟩

/-- **The Flat Norm** (Federer-Fleming, 1960).
    The flat norm of a current T is the infimum of M(S) + M(R) such that T = S + ∂R:
    F(T) = inf { M(S) + M(R) : T = S + ∂R }

    Reference: [H. Federer and W.H. Fleming, "Normal and integral currents", 1960]. -/
def flatNorm {k : ℕ} (T : Current n X k) : ℝ :=
  sInf (flatNormDecompSet T)

/-! ## Basic Properties (Proven) -/

/-- The flat norm is non-negative (Federer-Fleming 1960).
    Proof: Every element of the decomposition set is ≥ 0, so the infimum is ≥ 0. -/
theorem flatNorm_nonneg {k : ℕ} (T : Current n X k) : flatNorm T ≥ 0 := by
  unfold flatNorm
  apply Real.sInf_nonneg
  exact flatNormDecompSet_nonneg T

/-- The flat norm of the zero current is zero.
    Proof: 0 = 0 + ∂0, so mass(0) + mass(0) = 0 is in the set.
    The infimum of a set containing 0 and bounded below by 0 equals 0. -/
theorem flatNorm_zero {k : ℕ} : flatNorm (0 : Current n X k) = 0 := by
  unfold flatNorm
  apply le_antisymm
  · -- Show sInf ≤ 0 by exhibiting 0 in the set
    apply csInf_le (flatNormDecompSet_bddBelow 0)
    use 0, 0
    refine ⟨?_, by simp [Current.mass_zero]⟩
    ext ω
    rw [Current.boundary_zero]
    show (0 : Current n X k).toFun ω = ((0 : Current n X k) + (0 : Current n X k)).toFun ω
    rw [Current.zero_add]
  · exact flatNorm_nonneg 0

/-- The flat norm is bounded above by the mass (Federer-Fleming 1960).
    Proof: T = T + ∂0 is a valid decomposition with cost M(T) + M(0) = M(T). -/
theorem flatNorm_le_mass {k : ℕ} (T : Current n X k) : flatNorm T ≤ Current.mass T := by
  unfold flatNorm
  apply csInf_le (flatNormDecompSet_bddBelow T)
  use T, 0
  refine ⟨?_, by simp [Current.mass_zero]⟩
  ext ω
  rw [Current.boundary_zero]
  show T.toFun ω = (T + (0 : Current n X k)).toFun ω
  rw [Current.add_zero]

/-- The flat norm of a boundary is at most the flat norm of the original current (Federer-Fleming).
    Proof: For any decomposition T = S + ∂R with cost M(S) + M(R):
    - ∂T = ∂S + ∂∂R = ∂S (since ∂∂ = 0 by boundary_boundary)
    - ∂T = ∂S = 0 + ∂S is a valid decomposition with cost M(0) + M(S) = M(S)
    - So flatNorm(∂T) ≤ M(S) ≤ M(S) + M(R).
    Taking infimum over all decompositions yields flatNorm(∂T) ≤ flatNorm(T). -/
theorem flatNorm_boundary_le {k : ℕ} (T : Current n X (k + 1)) :
    flatNorm (Current.boundary T) ≤ flatNorm T := by
  unfold flatNorm
  apply le_csInf (flatNormDecompSet_nonempty T)
  intro m ⟨S, R, hT, hm⟩
  have h_bdyT : Current.boundary T = Current.boundary S := by
    calc Current.boundary T = Current.boundary (S + Current.boundary R) := by rw [hT]
      _ = Current.boundary S + Current.boundary (Current.boundary R) := Current.boundary_add S _
      _ = Current.boundary S + 0 := by rw [Current.boundary_boundary]
      _ = Current.boundary S := Current.add_zero _
  have h_decomp : Current.mass (0 : Current n X k) + Current.mass S ∈
      flatNormDecompSet (Current.boundary T) := by
    use 0, S
    refine ⟨?_, rfl⟩
    ext ω
    rw [h_bdyT]
    show (Current.boundary S).toFun ω = ((0 : Current n X k) + Current.boundary S).toFun ω
    rw [Current.zero_add]
  have h_le : sInf (flatNormDecompSet (Current.boundary T)) ≤
      Current.mass (0 : Current n X k) + Current.mass S :=
    csInf_le (flatNormDecompSet_bddBelow _) h_decomp
  rw [Current.mass_zero, zero_add] at h_le
  calc sInf (flatNormDecompSet (Current.boundary T)) ≤ Current.mass S := h_le
    _ ≤ Current.mass S + Current.mass R := le_add_of_nonneg_right (Current.mass_nonneg R)
    _ = m := hm.symm

/-- The flat norm of a boundary is bounded by the mass. -/
theorem flatNorm_boundary_le_mass {k : ℕ} (T : Current n X (k + 1)) :
    flatNorm (Current.boundary T) ≤ Current.mass T := by
  unfold flatNorm
  apply csInf_le (flatNormDecompSet_bddBelow (Current.boundary T))
  use 0, T
  refine ⟨?_, by simp [Current.mass_zero]⟩
  ext ω
  show (Current.boundary T).toFun ω = ((0 : Current n X k) + Current.boundary T).toFun ω
  rw [Current.zero_add]

/-! ## Axioms for Properties Requiring Deeper Infrastructure -/

/-- Negation reverses addition of currents. -/
theorem Current.neg_add {k : ℕ} (S T : Current n X k) : -(S + T) = -S + -T := by
  ext ω
  show -(S.toFun ω + T.toFun ω) = -S.toFun ω + -T.toFun ω
  ring

/-- Boundary commutes with negation. -/
theorem Current.boundary_neg' {k : ℕ} (R : Current n X (k + 1)) :
    Current.boundary (-R) = -Current.boundary R := by
  ext ω
  show (-R).toFun (smoothExtDeriv ω) = -(R.toFun (smoothExtDeriv ω))
  rfl

/-- The flat norm is symmetric under negation (Federer-Fleming 1960).
    Proof: If T = S + ∂R is a decomposition, then -T = -S + ∂(-R) is a decomposition with
    the same cost (since mass(-S) = mass(S) and mass(-R) = mass(R)).
    Thus the decomposition sets for T and -T have identical values. -/
theorem flatNorm_neg {k : ℕ} (T : Current n X k) : flatNorm (-T) = flatNorm T := by
  unfold flatNorm
  apply le_antisymm
  · -- Show flatNorm(-T) ≤ flatNorm(T)
    apply csInf_le_csInf (flatNormDecompSet_bddBelow (-T)) (flatNormDecompSet_nonempty T)
    -- For any m in decomp(T), show m is in decomp(-T)
    intro m ⟨S, R, hT, hm⟩
    -- If T = S + ∂R, then -T = -S + ∂(-R)
    use -S, -R
    refine ⟨?_, ?_⟩
    · -- -T = -S + ∂(-R)
      ext ω
      rw [Current.boundary_neg']
      have h := congrArg (fun T' => (-T').toFun ω) hT
      simp only [Current.neg_add] at h
      exact h
    · -- cost is the same
      rw [hm, Current.mass_neg, Current.mass_neg]
  · -- Show flatNorm(T) ≤ flatNorm(-T) by symmetry
    apply csInf_le_csInf (flatNormDecompSet_bddBelow T) (flatNormDecompSet_nonempty (-T))
    intro m ⟨S, R, hT, hm⟩
    -- If -T = S + ∂R, then T = -S + ∂(-R)
    use -S, -R
    refine ⟨?_, ?_⟩
    · ext ω
      rw [Current.boundary_neg']
      have h := congrArg (fun T' => (-T').toFun ω) hT
      simp only [Current.neg_add] at h
      -- h says: -(-T).toFun ω = (-S).toFun ω + (-∂R).toFun ω
      -- We need: T.toFun ω = (-S).toFun ω + (∂(-R)).toFun ω
      -- Since --T = T and ∂(-R) = -∂R:
      have h2 : (-(-T)).toFun ω = T.toFun ω := by
        show -(-T.toFun ω) = T.toFun ω
        ring
      rw [← h2, h]
    · rw [hm, Current.mass_neg, Current.mass_neg]

/-- Helper lemma: if for all pairs (m₁, m₂) from two sets there exists an element
    in another set that is ≤ m₁ + m₂, then the infimum of the third set is ≤ sum of infima. -/
private theorem sInf_add_helper {S₁ S₂ S : Set ℝ}
    (hS_ne : S.Nonempty) (hS_bdd : BddBelow S)
    (hS₁_ne : S₁.Nonempty) (hS₁_bdd : BddBelow S₁)
    (hS₂_ne : S₂.Nonempty) (hS₂_bdd : BddBelow S₂)
    (h : ∀ m₁ ∈ S₁, ∀ m₂ ∈ S₂, ∃ m ∈ S, m ≤ m₁ + m₂) :
    sInf S ≤ sInf S₁ + sInf S₂ := by
  -- For any ε > 0, there exist m₁ ∈ S₁ and m₂ ∈ S₂ with m₁ < sInf S₁ + ε/2 and m₂ < sInf S₂ + ε/2
  -- Then by h, there exists m ∈ S with m ≤ m₁ + m₂ < sInf S₁ + sInf S₂ + ε
  -- So sInf S ≤ sInf S₁ + sInf S₂ + ε for all ε > 0
  by_contra hne
  push_neg at hne
  -- hne : sInf S₁ + sInf S₂ < sInf S
  -- Let gap = sInf S - (sInf S₁ + sInf S₂) > 0
  set gap := sInf S - (sInf S₁ + sInf S₂) with hgap_def
  have hgap_pos : gap > 0 := by linarith
  -- There exist m₁ ∈ S₁ with m₁ < sInf S₁ + gap/3
  have ⟨m₁, hm₁_in, hm₁_lt⟩ := exists_lt_of_csInf_lt hS₁_ne (by linarith : sInf S₁ < sInf S₁ + gap / 3)
  -- There exist m₂ ∈ S₂ with m₂ < sInf S₂ + gap/3
  have ⟨m₂, hm₂_in, hm₂_lt⟩ := exists_lt_of_csInf_lt hS₂_ne (by linarith : sInf S₂ < sInf S₂ + gap / 3)
  -- By h, there exists m ∈ S with m ≤ m₁ + m₂
  obtain ⟨m, hm_in, hm_le⟩ := h m₁ hm₁_in m₂ hm₂_in
  -- But m ≤ m₁ + m₂ < sInf S₁ + gap/3 + sInf S₂ + gap/3 = sInf S₁ + sInf S₂ + 2*gap/3
  have hm_lt : m < sInf S₁ + sInf S₂ + 2 * gap / 3 := calc
    m ≤ m₁ + m₂ := hm_le
    _ < (sInf S₁ + gap / 3) + (sInf S₂ + gap / 3) := by linarith
    _ = sInf S₁ + sInf S₂ + 2 * gap / 3 := by ring
  -- And sInf S ≤ m < sInf S₁ + sInf S₂ + 2*gap/3 = sInf S - gap/3
  have h_contra : sInf S < sInf S := calc
    sInf S ≤ m := csInf_le hS_bdd hm_in
    _ < sInf S₁ + sInf S₂ + 2 * gap / 3 := hm_lt
    _ = sInf S - gap / 3 := by rw [hgap_def]; ring
    _ < sInf S := by linarith
  linarith

/-- The flat norm satisfies the triangle inequality (Federer-Fleming 1960).
    Proof: If T₁ = S₁ + ∂R₁ and T₂ = S₂ + ∂R₂,
    then T₁ + T₂ = (S₁+S₂) + ∂(R₁+R₂) with cost M(S₁+S₂) + M(R₁+R₂)
    ≤ M(S₁) + M(S₂) + M(R₁) + M(R₂) by triangle inequalities on mass. -/
theorem flatNorm_add_le {k : ℕ} (T₁ T₂ : Current n X k) :
    flatNorm (T₁ + T₂) ≤ flatNorm T₁ + flatNorm T₂ := by
  unfold flatNorm
  apply sInf_add_helper (flatNormDecompSet_nonempty (T₁ + T₂))
    (flatNormDecompSet_bddBelow (T₁ + T₂)) (flatNormDecompSet_nonempty T₁)
    (flatNormDecompSet_bddBelow T₁) (flatNormDecompSet_nonempty T₂)
    (flatNormDecompSet_bddBelow T₂)
  intro m₁ hm₁ m₂ hm₂
  obtain ⟨S₁, R₁, hT₁, hm₁_eq⟩ := hm₁
  obtain ⟨S₂, R₂, hT₂, hm₂_eq⟩ := hm₂
  -- T₁ + T₂ = (S₁ + S₂) + ∂(R₁ + R₂)
  have h_decomp : T₁ + T₂ = (S₁ + S₂) + Current.boundary (R₁ + R₂) := by
    rw [hT₁, hT₂, Current.boundary_add]
    ext ω
    show S₁.toFun ω + (Current.boundary R₁).toFun ω + (S₂.toFun ω + (Current.boundary R₂).toFun ω) =
         S₁.toFun ω + S₂.toFun ω + ((Current.boundary R₁).toFun ω + (Current.boundary R₂).toFun ω)
    ring
  have h_cost_in : Current.mass (S₁ + S₂) + Current.mass (R₁ + R₂) ∈ flatNormDecompSet (T₁ + T₂) := by
    refine ⟨S₁ + S₂, R₁ + R₂, h_decomp, rfl⟩
  have h_cost_le : Current.mass (S₁ + S₂) + Current.mass (R₁ + R₂) ≤ m₁ + m₂ := by
    rw [hm₁_eq, hm₂_eq]
    calc Current.mass (S₁ + S₂) + Current.mass (R₁ + R₂)
      ≤ (Current.mass S₁ + Current.mass S₂) + (Current.mass R₁ + Current.mass R₂) :=
        add_le_add (Current.mass_add_le S₁ S₂) (Current.mass_add_le R₁ R₂)
      _ = Current.mass S₁ + Current.mass R₁ + (Current.mass S₂ + Current.mass R₂) := by ring
  exact ⟨Current.mass (S₁ + S₂) + Current.mass (R₁ + R₂), h_cost_in, h_cost_le⟩

/-- Scalar multiplication distributes over current addition. -/
theorem Current.smul_add {k : ℕ} (c : ℝ) (S T : Current n X k) :
    c • (S + T) = c • S + c • T := by
  ext ω
  show c * (S.toFun ω + T.toFun ω) = c * S.toFun ω + c * T.toFun ω
  ring

/-- Scalar multiplication distributes over current subtraction. -/
theorem Current.smul_sub {k : ℕ} (c : ℝ) (S T : Current n X k) :
    c • (S - T) = c • S - c • T := by
  ext ω
  show c * (S.toFun ω - T.toFun ω) = c * S.toFun ω - c * T.toFun ω
  ring

/-- Scalar multiplication associates. -/
theorem Current.smul_smul {k : ℕ} (c d : ℝ) (T : Current n X k) :
    c • (d • T) = (c * d) • T := by
  ext ω
  show c * (d * T.toFun ω) = (c * d) * T.toFun ω
  ring

/-- Helper: decomposition sets scale with |c|. If m ∈ decomp(T), then |c|*m ∈ decomp(c•T). -/
private theorem flatNormDecompSet_smul_mem {k : ℕ} (c : ℝ) (T : Current n X k)
    (m : ℝ) (hm : m ∈ flatNormDecompSet T) :
    |c| * m ∈ flatNormDecompSet (c • T) := by
  obtain ⟨S, R, hT, hm_eq⟩ := hm
  -- c•T = c•S + ∂(c•R)
  have h_decomp : c • T = c • S + Current.boundary (c • R) := by
    rw [hT, Current.smul_add, Current.boundary_smul]
  refine ⟨c • S, c • R, h_decomp, ?_⟩
  rw [hm_eq, Current.mass_smul, Current.mass_smul]
  ring

/-- Helper: decomposition sets scale with |c| inversely when c ≠ 0. -/
private theorem flatNormDecompSet_smul_inv {k : ℕ} (c : ℝ) (hc : c ≠ 0) (T : Current n X k)
    (m : ℝ) (hm : m ∈ flatNormDecompSet (c • T)) :
    m / |c| ∈ flatNormDecompSet T := by
  obtain ⟨S, R, hcT, hm_eq⟩ := hm
  -- T = (1/c)•(c•T) = (1/c)•S + ∂((1/c)•R)
  have h_decomp : T = c⁻¹ • S + Current.boundary (c⁻¹ • R) := by
    have h_inv_smul : c⁻¹ • (c • T) = T := by
      rw [Current.smul_smul, inv_mul_cancel₀ hc]
      ext ω
      show (1 : ℝ) * T.toFun ω = T.toFun ω
      ring
    rw [← h_inv_smul, hcT, Current.smul_add, Current.boundary_smul]
  refine ⟨c⁻¹ • S, c⁻¹ • R, h_decomp, ?_⟩
  rw [hm_eq, Current.mass_smul, Current.mass_smul]
  have habs_ne : |c| ≠ 0 := abs_ne_zero.mpr hc
  have h_abs_inv : |c⁻¹| = |c|⁻¹ := abs_inv c
  rw [h_abs_inv]
  field_simp

/-- One-form smul identity. -/
theorem Current.one_smul {k : ℕ} (T : Current n X k) : (1 : ℝ) • T = T := by
  ext ω
  show (1 : ℝ) * T.toFun ω = T.toFun ω
  ring

/-- Zero smul gives zero current. -/
theorem Current.zero_smul {k : ℕ} (T : Current n X k) : (0 : ℝ) • T = 0 := by
  ext ω
  show (0 : ℝ) * T.toFun ω = (0 : Current n X k).toFun ω
  simp only [MulZeroClass.zero_mul]
  rfl

theorem flatNorm_smul {k : ℕ} (c : ℝ) (T : Current n X k) :
    flatNorm (c • T) = |c| * flatNorm T := by
  by_cases hc : c = 0
  · simp only [hc, abs_zero, MulZeroClass.zero_mul, Current.zero_smul, flatNorm_zero]
  · -- Case c ≠ 0, so |c| > 0
    have hc_abs_pos : |c| > 0 := abs_pos.mpr hc
    have hc_abs_ne : |c| ≠ 0 := abs_ne_zero.mpr hc
    apply le_antisymm
    · -- flatNorm(c•T) ≤ |c| * flatNorm(T)
      by_contra h_not_le
      push_neg at h_not_le
      set gap := flatNorm (c • T) - |c| * flatNorm T with hgap_def
      have hgap_pos : gap > 0 := by linarith
      have heps_pos : gap / (2 * |c|) > 0 := by positivity
      have ⟨m, hm_in, hm_lt⟩ := exists_lt_of_csInf_lt (flatNormDecompSet_nonempty T)
        (by linarith : flatNorm T < flatNorm T + gap / (2 * |c|))
      have h_scaled_in := flatNormDecompSet_smul_mem c T m hm_in
      have h_scaled_lt : |c| * m < |c| * flatNorm T + gap / 2 := by
        have h1 : |c| * m < |c| * (flatNorm T + gap / (2 * |c|)) :=
          mul_lt_mul_of_pos_left hm_lt hc_abs_pos
        calc |c| * m < |c| * (flatNorm T + gap / (2 * |c|)) := h1
          _ = |c| * flatNorm T + |c| * (gap / (2 * |c|)) := by ring
          _ = |c| * flatNorm T + gap / 2 := by field_simp
      have h_sInf_le : flatNorm (c • T) ≤ |c| * m :=
        csInf_le (flatNormDecompSet_bddBelow (c • T)) h_scaled_in
      linarith
    · -- flatNorm(c•T) ≥ |c| * flatNorm(T)
      apply le_csInf (flatNormDecompSet_nonempty (c • T))
      intro m hm
      have h_in := flatNormDecompSet_smul_inv c hc T m hm
      have hsInf_le : flatNorm T ≤ m / |c| :=
        csInf_le (flatNormDecompSet_bddBelow T) h_in
      calc |c| * flatNorm T
        ≤ |c| * (m / |c|) := mul_le_mul_of_nonneg_left hsInf_le (le_of_lt hc_abs_pos)
        _ = m := by field_simp

/-- Flat norm of difference is bounded by sum of flat norms.
    Follows from triangle inequality and symmetry under negation. -/
theorem flatNorm_sub_le {k : ℕ} (S T : Current n X k) :
    flatNorm (S - T) ≤ flatNorm S + flatNorm T := by
  -- S - T = S + (-T)
  calc flatNorm (S - T) = flatNorm (S + -T) := rfl
    _ ≤ flatNorm S + flatNorm (-T) := flatNorm_add_le S (-T)
    _ = flatNorm S + flatNorm T := by rw [flatNorm_neg]

/-- **Bound evaluation by mass** (Federer 1969, §4.1).
    This is the defining property of mass as the dual norm to comass.
    For any current T and form ψ: |T(ψ)| ≤ mass(T) × comass(ψ).

    **Proof**: The mass is defined as mass(T) = sup { |T(ω)| : comass(ω) ≤ 1 }.
    - If comass(ψ) = 0, we use the boundedness of T to show |T(ψ)| = 0.
    - If comass(ψ) > 0, normalize ψ to ψ' = ψ/comass(ψ) with comass 1.
      Then |T(ψ')| ≤ mass(T) by definition, and |T(ψ)| = comass(ψ) × |T(ψ')|.

    Reference: [H. Federer, "Geometric Measure Theory", Springer 1969, §4.1]. -/
theorem eval_le_mass {k : ℕ} (T : Current n X k) (ψ : SmoothForm n X k) :
    |T.toFun ψ| ≤ Current.mass T * comass ψ := by
  by_cases h_zero : comass ψ = 0
  · -- Case: comass ψ = 0
    obtain ⟨M, hM⟩ := T.is_bounded
    have h_bound : |T.toFun ψ| ≤ M * comass ψ := hM ψ
    rw [h_zero, MulZeroClass.mul_zero] at h_bound
    have h_nonneg : |T.toFun ψ| ≥ 0 := abs_nonneg _
    have h_eq_zero : |T.toFun ψ| = 0 := le_antisymm h_bound h_nonneg
    rw [h_eq_zero, h_zero, MulZeroClass.mul_zero]
  · -- Case: comass ψ > 0
    have h_pos : comass ψ > 0 := lt_of_le_of_ne (comass_nonneg ψ) (Ne.symm h_zero)
    let c : ℝ := (comass ψ)⁻¹
    let ψ' : SmoothForm n X k := c • ψ
    have h_c_pos : c > 0 := inv_pos_of_pos h_pos
    have h_comass_ψ' : comass ψ' ≤ 1 := by
      show comass (c • ψ) ≤ 1
      rw [comass_smul, abs_of_pos h_c_pos]
      show (comass ψ)⁻¹ * comass ψ ≤ 1
      rw [inv_mul_cancel₀ h_zero]
    have h_in_set : |T.toFun ψ'| ∈ { r : ℝ | ∃ ω : SmoothForm n X k, comass ω ≤ 1 ∧ r = |T.toFun ω| } :=
      ⟨ψ', h_comass_ψ', rfl⟩
    have h_le_mass : |T.toFun ψ'| ≤ Current.mass T := by
      unfold Current.mass
      exact le_csSup (Current.mass_set_bddAbove T) h_in_set
    have h_eval : T.toFun ψ = comass ψ * T.toFun ψ' := by
      have h_prod_eq : comass ψ • ψ' = ψ := by
        show comass ψ • (c • ψ) = ψ
        rw [smul_smul, mul_inv_cancel₀ h_zero, one_smul]
      have h_map : T.toFun (comass ψ • ψ') = comass ψ * T.toFun ψ' := Current.map_smul T (comass ψ) ψ'
      rw [h_prod_eq] at h_map
      exact h_map
    calc |T.toFun ψ|
        = |comass ψ * T.toFun ψ'| := by rw [h_eval]
      _ = |comass ψ| * |T.toFun ψ'| := abs_mul _ _
      _ = comass ψ * |T.toFun ψ'| := by rw [abs_of_pos h_pos]
      _ ≤ comass ψ * Current.mass T := mul_le_mul_of_nonneg_left h_le_mass (le_of_lt h_pos)
      _ = Current.mass T * comass ψ := mul_comm _ _

/-! ## Finite-sum flat-norm bounds (TeX “transport ⇒ flat control” scaffolding)

These lemmas are purely formal consequences of:
- the definition of `flatNorm` as an infimum over decompositions `T = S + ∂R`
- the triangle inequality `flatNorm_add_le`

They are the Lean core needed for TeX Proposition `prop:transport-flat-glue-weighted`:
given a matching of pieces across a face and a per-piece flat decomposition estimate,
one gets a bound on the flat norm of the total mismatch current.
-/

namespace Hodge.FlatNormFinite

/-- A recursion-only “sum over `Fin N`” that avoids requiring algebraic instances on `Current`. -/
def finSum {k : ℕ} : ∀ (N : ℕ), (Fin N → Current n X k) → Current n X k
  | 0, _ => 0
  | N + 1, f => f 0 + finSum N (fun i => f i.succ)

/-- A recursion-only “sum over `Fin N`” for real costs. -/
def finSumℝ : ∀ (N : ℕ), (Fin N → ℝ) → ℝ
  | 0, _ => 0
  | N + 1, f => f 0 + finSumℝ N (fun i => f i.succ)

@[simp] theorem finSum_zero {k : ℕ} (f : Fin 0 → Current n X k) : finSum (n := n) (X := X) 0 f = 0 := rfl
@[simp] theorem finSumℝ_zero (f : Fin 0 → ℝ) : finSumℝ 0 f = 0 := rfl

@[simp] theorem finSum_succ {k : ℕ} (N : ℕ) (f : Fin (N + 1) → Current n X k) :
    finSum (n := n) (X := X) (N + 1) f = f 0 + finSum (n := n) (X := X) N (fun i => f i.succ) := rfl

@[simp] theorem finSumℝ_succ (N : ℕ) (f : Fin (N + 1) → ℝ) :
    finSumℝ (N + 1) f = f 0 + finSumℝ N (fun i => f i.succ) := rfl

/-- `finSum` agrees with the standard `Fintype` sum over `Fin N`. -/
theorem finSum_eq_sum_univ {k : ℕ} :
    ∀ (N : ℕ) (T : Fin N → Current n X k),
      finSum (n := n) (X := X) (k := k) N T = ∑ i : Fin N, T i
  | 0, T => by
      simp [finSum]
  | N + 1, T => by
      -- `∑ i : Fin (N+1), T i = T 0 + ∑ i : Fin N, T i.succ`
      simpa [finSum, Fin.sum_univ_succ, finSum_eq_sum_univ (N := N) (T := fun i => T i.succ)]

/-- `finSumℝ` agrees with the standard `Fintype` sum over `Fin N`. -/
theorem finSumℝ_eq_sum_univ :
    ∀ (N : ℕ) (cost : Fin N → ℝ),
      finSumℝ N cost = ∑ i : Fin N, cost i
  | 0, cost => by
      simp [finSumℝ]
  | N + 1, cost => by
      simpa [finSumℝ, Fin.sum_univ_succ, finSumℝ_eq_sum_univ (N := N) (cost := fun i => cost i.succ)]

/-- If `T = S + ∂R`, then `flatNorm T ≤ mass S + mass R` (by definition of infimum). -/
theorem flatNorm_le_mass_add_mass_of_decomp {k : ℕ}
    (T : Current n X k) (S : Current n X k) (R : Current n X (k + 1))
    (hT : T = S + Current.boundary R) :
    _root_.flatNorm (n := n) (X := X) (k := k) T ≤ Current.mass S + Current.mass R := by
  -- `flatNorm T` is the infimum over all such decomposition costs.
  unfold _root_.flatNorm
  refine csInf_le (_root_.flatNormDecompSet_bddBelow (n := n) (X := X) (k := k) T) ?_
  refine ⟨S, R, hT, rfl⟩

/-- If `T` has a decomposition with total cost ≤ `c`, then `flatNorm T ≤ c`. -/
theorem flatNorm_le_of_exists_decomp_le {k : ℕ}
    (T : Current n X k) (c : ℝ)
    (h : ∃ (S : Current n X k) (R : Current n X (k + 1)),
      T = S + Current.boundary R ∧ Current.mass S + Current.mass R ≤ c) :
    _root_.flatNorm (n := n) (X := X) (k := k) T ≤ c := by
  rcases h with ⟨S, R, hT, hcost⟩
  exact le_trans (flatNorm_le_mass_add_mass_of_decomp (n := n) (X := X) (k := k) T S R hT) hcost

/-- Finite-sum bound: if each term has `flatNorm ≤ cost`, then the whole sum does too. -/
theorem flatNorm_finSum_le_of_forall {k : ℕ} :
    ∀ (N : ℕ) (T : Fin N → Current n X k) (cost : Fin N → ℝ),
      (∀ i, _root_.flatNorm (n := n) (X := X) (k := k) (T i) ≤ cost i) →
      _root_.flatNorm (n := n) (X := X) (k := k) (finSum (n := n) (X := X) (k := k) N T)
        ≤ finSumℝ N cost
  | 0, T, cost, _h => by
      simp [finSum, finSumℝ, _root_.flatNorm_zero (n := n) (X := X) (k := k)]
  | N + 1, T, cost, h => by
      -- Split off the head and apply triangle inequality.
      have h0 : _root_.flatNorm (n := n) (X := X) (k := k) (T 0) ≤ cost 0 := h 0
      have htail :
          _root_.flatNorm (n := n) (X := X) (k := k)
              (finSum (n := n) (X := X) (k := k) N (fun i => T i.succ))
            ≤ finSumℝ N (fun i => cost i.succ) :=
        flatNorm_finSum_le_of_forall N (fun i => T i.succ) (fun i => cost i.succ) (fun i => h i.succ)
      calc
        _root_.flatNorm (n := n) (X := X) (k := k)
            (finSum (n := n) (X := X) (k := k) (N + 1) T)
            = _root_.flatNorm (n := n) (X := X) (k := k)
                (T 0 + finSum (n := n) (X := X) (k := k) N (fun i => T i.succ)) := by
                  simp [finSum]
        _ ≤ _root_.flatNorm (n := n) (X := X) (k := k) (T 0) +
              _root_.flatNorm (n := n) (X := X) (k := k)
                (finSum (n := n) (X := X) (k := k) N (fun i => T i.succ)) := by
                  simpa using
                    (_root_.flatNorm_add_le (n := n) (X := X) (k := k)
                      (T 0) (finSum (n := n) (X := X) (k := k) N (fun i => T i.succ)))
        _ ≤ cost 0 + finSumℝ N (fun i => cost i.succ) := by
              exact add_le_add h0 htail
        _ = finSumℝ (N + 1) cost := by
              simp [finSumℝ]

end Hodge.FlatNormFinite

/-!
## Finset-sum triangle inequality for `flatNorm`

This is a convenience wrapper around `flatNorm_add_le`, allowing later TeX-spine code to use the
standard `Finset.sum` API directly.
-/

theorem flatNorm_sum_le_sum_flatNorm {ι : Type*} {k : ℕ}
    (s : Finset ι) (T : ι → Current n X k) :
    flatNorm (n := n) (X := X) (k := k) (∑ i ∈ s, T i)
      ≤ ∑ i ∈ s, flatNorm (n := n) (X := X) (k := k) (T i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [flatNorm_zero]
  · intro a s ha ih
    have h1 :
        flatNorm (n := n) (X := X) (k := k) (T a + ∑ i ∈ s, T i)
          ≤ flatNorm (n := n) (X := X) (k := k) (T a) +
              flatNorm (n := n) (X := X) (k := k) (∑ i ∈ s, T i) := by
      simpa using
        (flatNorm_add_le (n := n) (X := X) (k := k) (T a) (∑ i ∈ s, T i))
    have h2 :
        flatNorm (n := n) (X := X) (k := k) (T a) +
            flatNorm (n := n) (X := X) (k := k) (∑ i ∈ s, T i)
          ≤ flatNorm (n := n) (X := X) (k := k) (T a) +
              ∑ i ∈ s, flatNorm (n := n) (X := X) (k := k) (T i) :=
      add_le_add_right ih (flatNorm (n := n) (X := X) (k := k) (T a))
    have h := le_trans h1 h2
    simpa [Finset.sum_insert ha] using h

/-- Helper: For any decomposition T = S + ∂R, evaluation is bounded by
    (mass(S) + mass(R)) × max(comass ψ, comass dψ). -/
theorem eval_le_decomp_cost {k : ℕ} (T S : Current n X k) (R : Current n X (k + 1))
    (h : T = S + Current.boundary R) (ψ : SmoothForm n X k) :
    |T.toFun ψ| ≤ (Current.mass S + Current.mass R) * max (comass ψ) (comass (smoothExtDeriv ψ)) := by
  have h_eval : T.toFun ψ = S.toFun ψ + R.toFun (smoothExtDeriv ψ) := by rw [h]; rfl
  have h_tri : |S.toFun ψ + R.toFun (smoothExtDeriv ψ)| ≤
      |S.toFun ψ| + |R.toFun (smoothExtDeriv ψ)| := abs_add_le _ _
  have h_S : |S.toFun ψ| ≤ Current.mass S * comass ψ := eval_le_mass S ψ
  have h_R : |R.toFun (smoothExtDeriv ψ)| ≤ Current.mass R * comass (smoothExtDeriv ψ) :=
    eval_le_mass R (smoothExtDeriv ψ)
  have h_S' : Current.mass S * comass ψ ≤
      Current.mass S * max (comass ψ) (comass (smoothExtDeriv ψ)) :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) (Current.mass_nonneg S)
  have h_R' : Current.mass R * comass (smoothExtDeriv ψ) ≤
      Current.mass R * max (comass ψ) (comass (smoothExtDeriv ψ)) :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) (Current.mass_nonneg R)
  rw [h_eval]
  calc |S.toFun ψ + R.toFun (smoothExtDeriv ψ)|
      ≤ |S.toFun ψ| + |R.toFun (smoothExtDeriv ψ)| := h_tri
    _ ≤ Current.mass S * comass ψ + Current.mass R * comass (smoothExtDeriv ψ) := by linarith
    _ ≤ Current.mass S * max (comass ψ) (comass (smoothExtDeriv ψ)) +
        Current.mass R * max (comass ψ) (comass (smoothExtDeriv ψ)) := by linarith
    _ = (Current.mass S + Current.mass R) * max (comass ψ) (comass (smoothExtDeriv ψ)) := by ring

/-- **Federer-Fleming Evaluation Estimate** (Federer-Fleming, 1960).
    The evaluation of a current on a smooth form is bounded by the flat norm of the
    current and the maximum comass of the form and its derivative.

    **Proof**: For any decomposition T = S + ∂R, |T(ψ)| ≤ (M(S)+M(R)) × max(comass).
    Since flatNorm is the infimum of M(S)+M(R), the bound follows.

    Reference: [H. Federer and W.H. Fleming, "Normal and integral currents", 1960]. -/
theorem eval_le_flatNorm {k : ℕ} (T : Current n X k) (ψ : SmoothForm n X k) :
    |T.toFun ψ| ≤ flatNorm T * max (comass ψ) (comass (smoothExtDeriv ψ)) := by
  unfold flatNorm
  have h_bound : ∀ m ∈ flatNormDecompSet T,
      |T.toFun ψ| ≤ m * max (comass ψ) (comass (smoothExtDeriv ψ)) := by
    intro m ⟨S, R, hT, hm⟩
    rw [hm]
    exact eval_le_decomp_cost T S R hT ψ
  by_cases h_zero : max (comass ψ) (comass (smoothExtDeriv ψ)) = 0
  · have h1 : comass ψ = 0 := by
      have := le_max_left (comass ψ) (comass (smoothExtDeriv ψ))
      linarith [comass_nonneg ψ]
    obtain ⟨m, hm⟩ := flatNormDecompSet_nonempty T
    have h := h_bound m hm
    rw [h_zero] at h; simp at h
    rw [h, h_zero]; simp
  · have h_pos : max (comass ψ) (comass (smoothExtDeriv ψ)) > 0 :=
      lt_of_le_of_ne (le_max_of_le_left (comass_nonneg ψ)) (Ne.symm h_zero)
    have h_div : |T.toFun ψ| / max (comass ψ) (comass (smoothExtDeriv ψ)) ≤
        sInf (flatNormDecompSet T) := by
      apply le_csInf (flatNormDecompSet_nonempty T)
      intro m hm
      exact (div_le_iff₀ h_pos).mpr (h_bound m hm)
    calc |T.toFun ψ| = |T.toFun ψ| / max (comass ψ) (comass (smoothExtDeriv ψ)) *
          max (comass ψ) (comass (smoothExtDeriv ψ)) := by field_simp
      _ ≤ sInf (flatNormDecompSet T) * max (comass ψ) (comass (smoothExtDeriv ψ)) :=
          mul_le_mul_of_nonneg_right h_div (le_of_lt h_pos)

/-- A current is zero iff its flat norm is zero (Federer-Fleming).
    The ← direction follows from flatNorm_zero.
    The → direction: if flatNorm(T) = 0, then by eval_le_flatNorm,
    |T(ψ)| ≤ 0 for all ψ, so T(ψ) = 0 for all ψ, hence T = 0 by extensionality. -/
theorem flatNorm_eq_zero_iff {k : ℕ} (T : Current n X k) : flatNorm T = 0 ↔ T = 0 := by
  constructor
  · intro h_norm_zero
    ext ψ
    have h_bound := eval_le_flatNorm T ψ
    rw [h_norm_zero, MulZeroClass.zero_mul] at h_bound
    have h_nonneg : |T.toFun ψ| ≥ 0 := abs_nonneg _
    have h_eq_zero : |T.toFun ψ| = 0 := le_antisymm h_bound h_nonneg
    exact abs_eq_zero.mp h_eq_zero
  · intro h_T_zero
    rw [h_T_zero]
    exact flatNorm_zero

/-! ## Flat Norm Convergence and Limit Bounds (Agent 3 - 2b) -/

/-- **Flat norm convergence** (Federer-Fleming 1960).
    A sequence of currents `Tᵢ` converges to `T` in flat norm if `flatNorm(Tᵢ - T) → 0`. -/
def FlatNormConverges {k : ℕ} (seq : ℕ → Current n X k) (T : Current n X k) : Prop :=
  Filter.Tendsto (fun i => flatNorm (seq i - T)) Filter.atTop (nhds 0)

/-- **Pointwise convergence from flat norm convergence** (Federer-Fleming).
    If `Tᵢ → T` in flat norm, then for each form ψ, `Tᵢ(ψ) → T(ψ)`.

    **Proof**: By `eval_le_flatNorm`, |Tᵢ(ψ) - T(ψ)| = |(Tᵢ - T)(ψ)| ≤ flatNorm(Tᵢ - T) × C
    where C = max(comass ψ, comass dψ). Since flatNorm(Tᵢ - T) → 0, the RHS → 0. -/
theorem flatNormConverges_pointwise {k : ℕ} {seq : ℕ → Current n X k} {T : Current n X k}
    (h_conv : FlatNormConverges seq T) (ψ : SmoothForm n X k) :
    Filter.Tendsto (fun i => (seq i).toFun ψ) Filter.atTop (nhds (T.toFun ψ)) := by
  -- The constant C for this form
  let C := max (comass ψ) (comass (smoothExtDeriv ψ))
  -- For each i: |seq(i)(ψ) - T(ψ)| ≤ flatNorm(seq i - T) * C
  have h_bound : ∀ i, |((seq i).toFun ψ) - (T.toFun ψ)| ≤ flatNorm (seq i - T) * C := fun i => by
    -- (seq i - T).toFun ψ = seq(i)(ψ) - T(ψ)
    have h_diff : (seq i - T).toFun ψ = (seq i).toFun ψ - T.toFun ψ := rfl
    have h := eval_le_flatNorm (seq i - T) ψ
    rwa [h_diff] at h
  -- flatNorm(seq i - T) → 0 by hypothesis
  -- So flatNorm(seq i - T) * C → 0 * C = 0
  have h_prod_tends : Filter.Tendsto (fun i => flatNorm (seq i - T) * C) Filter.atTop (nhds 0) := by
    have h_mul := Filter.Tendsto.mul h_conv (tendsto_const_nhds (x := C))
    simp only [MulZeroClass.zero_mul] at h_mul
    exact h_mul
  -- By squeeze theorem: |seq(i)(ψ) - T(ψ)| → 0
  rw [Metric.tendsto_atTop] at h_prod_tends ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := h_prod_tends ε hε
  use N
  intro i hi
  have h1 := hN i hi
  simp only [Real.dist_eq, sub_zero] at h1
  have h2 := h_bound i
  have h3 : |flatNorm (seq i - T) * C| = flatNorm (seq i - T) * C := by
    apply abs_of_nonneg
    exact mul_nonneg (flatNorm_nonneg _) (le_max_of_le_left (comass_nonneg ψ))
  rw [h3] at h1
  rw [Real.dist_eq]
  linarith

/-- **Boundary bound constant** (extract the M from boundary_bound field).
    For k > 0, this extracts the bound M such that |T(dω)| ≤ M * comass(ω) for all ω. -/
noncomputable def boundaryBoundConst {k : ℕ} (T : Current n X (k + 1)) : ℝ :=
  (T.boundary_bound).choose

/-- The boundary bound constant satisfies the bound property. -/
theorem boundaryBoundConst_spec {k : ℕ} (T : Current n X (k + 1)) :
    ∀ ω : SmoothForm n X k, |T.toFun (smoothExtDeriv ω)| ≤ boundaryBoundConst T * comass ω :=
  (T.boundary_bound).choose_spec

/-- **Limit currents preserve boundary boundedness** (Agent 3 - 2b).

    If a sequence of currents `Tᵢ → T` in flat norm, and all `Tᵢ` have uniformly
    bounded boundary constants (i.e., `boundaryBoundConst Tᵢ ≤ M` for all i),
    then the limit current `T` also satisfies boundary boundedness with constant `M`.

    **Proof Sketch**: For any form ω:
    - |T(dω)| = lim |Tᵢ(dω)| (by pointwise convergence)
    - |Tᵢ(dω)| ≤ Mᵢ * comass(ω) ≤ M * comass(ω) (by uniform bound)
    - Taking limit: |T(dω)| ≤ M * comass(ω)

    **Mathematical Reference**: [Federer-Fleming, "Normal and integral currents", 1960]
    Mass bounds are preserved under flat norm limits by compactness. -/
theorem limit_current_boundary_bound {k : ℕ} {seq : ℕ → Current n X (k + 1)}
    {T : Current n X (k + 1)} (h_conv : FlatNormConverges seq T)
    {M : ℝ} (h_unif : ∀ i, boundaryBoundConst (seq i) ≤ M) :
    ∀ ω : SmoothForm n X k, |T.toFun (smoothExtDeriv ω)| ≤ M * comass ω := by
  intro ω
  -- The sequence Tᵢ(dω) converges to T(dω)
  have h_pointwise := flatNormConverges_pointwise h_conv (smoothExtDeriv ω)
  -- For each i: |Tᵢ(dω)| ≤ boundaryBoundConst(Tᵢ) * comass(ω) ≤ M * comass(ω)
  have h_seq_bound : ∀ i, |(seq i).toFun (smoothExtDeriv ω)| ≤ M * comass ω := fun i => by
    have h1 := boundaryBoundConst_spec (seq i) ω
    have h2 := h_unif i
    have h_comass_nonneg : comass ω ≥ 0 := comass_nonneg ω
    calc |(seq i).toFun (smoothExtDeriv ω)|
        ≤ boundaryBoundConst (seq i) * comass ω := h1
      _ ≤ M * comass ω := mul_le_mul_of_nonneg_right h2 h_comass_nonneg
  -- The limit of a bounded sequence is bounded by the same bound
  -- Use: if aᵢ → a and |aᵢ| ≤ B for all i, then |a| ≤ B
  by_contra h_not_le
  push_neg at h_not_le
  -- |T(dω)| > M * comass(ω), so there exists gap > 0
  set gap := |T.toFun (smoothExtDeriv ω)| - M * comass ω with hgap_def
  have hgap_pos : gap > 0 := by linarith
  -- By convergence, ∃ N such that for i ≥ N, |Tᵢ(dω) - T(dω)| < gap/2
  rw [Metric.tendsto_atTop] at h_pointwise
  obtain ⟨N, hN⟩ := h_pointwise (gap / 2) (by linarith)
  -- For i = N: |T_N(dω) - T(dω)| < gap/2
  have h_close := hN N (le_refl N)
  rw [Real.dist_eq] at h_close
  -- |T_N(dω)| ≤ M * comass(ω) by h_seq_bound
  have h_N_bound := h_seq_bound N
  -- Reverse triangle inequality: ||a| - |b|| ≤ |a - b|
  have h_rev_tri := abs_sub_abs_le_abs_sub ((seq N).toFun (smoothExtDeriv ω)) (T.toFun (smoothExtDeriv ω))
  -- So |T(dω)| - |T_N(dω)| ≤ |T_N(dω) - T(dω)| < gap/2
  have h1 : |T.toFun (smoothExtDeriv ω)| - |(seq N).toFun (smoothExtDeriv ω)| ≤
      |(seq N).toFun (smoothExtDeriv ω) - T.toFun (smoothExtDeriv ω)| := by
    have := abs_sub_abs_le_abs_sub (T.toFun (smoothExtDeriv ω)) ((seq N).toFun (smoothExtDeriv ω))
    linarith [abs_sub_comm ((seq N).toFun (smoothExtDeriv ω)) (T.toFun (smoothExtDeriv ω))]
  -- So |T(dω)| ≤ |T_N(dω)| + gap/2 ≤ M * comass(ω) + gap/2 < M * comass(ω) + gap = |T(dω)|
  have h2 : |T.toFun (smoothExtDeriv ω)| ≤ M * comass ω + gap / 2 := by linarith
  -- But |T(dω)| = M * comass(ω) + gap by definition of gap
  have h3 : |T.toFun (smoothExtDeriv ω)| = M * comass ω + gap := by rw [hgap_def]; ring
  linarith

/-- **Limit current construction** (Agent 3 - 2b).

    Given a sequence of currents converging in flat norm with uniformly bounded
    properties, we can construct a limit current with the same properties.

    This is a key technical lemma for the Federer-Fleming compactness theorem. -/
theorem limit_current_exists {k : ℕ} {seq : ℕ → Current n X (k + 1)}
    {T : Current n X (k + 1)} (h_conv : FlatNormConverges seq T)
    {M_bound : ℝ} (h_bound_unif : ∀ i, boundaryBoundConst (seq i) ≤ M_bound) :
    ∃ M : ℝ, ∀ ω : SmoothForm n X k, |T.toFun (smoothExtDeriv ω)| ≤ M * comass ω :=
  ⟨M_bound, limit_current_boundary_bound h_conv h_bound_unif⟩

end
