import Hodge.Kahler.Manifolds
import Hodge.Analytic.Forms
import Mathlib.Tactic.Ring

noncomputable section

open Classical Hodge

universe u

inductive isPQForm (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [HasLocallyConstantCharts n X]
    : (p q : ℕ) → {k : ℕ} → (h : p + q = k) → (ω : SmoothForm n X k) → Prop where
  | zero (p q : ℕ) {k : ℕ} (h : p + q = k) :
      isPQForm n X p q h (0 : SmoothForm n X k)
  | unitForm : isPQForm n X 0 0 (by rfl) unitForm
  | omega [ProjectiveComplexManifold n X] (K : KahlerManifold n X) :
      isPQForm n X 1 1 (by rfl) K.omega_form
  | add {p q : ℕ} {k : ℕ} (h : p + q = k) {ω η : SmoothForm n X k} :
      isPQForm n X p q h ω → isPQForm n X p q h η → isPQForm n X p q h (ω + η)
  | neg {p q : ℕ} {k : ℕ} (h : p + q = k) {ω : SmoothForm n X k} :
      isPQForm n X p q h ω → isPQForm n X p q h (-ω)
  | smul {p q : ℕ} {k : ℕ} (h : p + q = k) (c : ℂ) {ω : SmoothForm n X k} :
      isPQForm n X p q h ω → isPQForm n X p q h (c • ω)
  | wedge {p q r s : ℕ} {k l : ℕ} (hpq : p + q = k) (hrs : r + s = l)
      {ω : SmoothForm n X k} {η : SmoothForm n X l} :
      isPQForm n X p q hpq ω → isPQForm n X r s hrs η →
      isPQForm n X (p + r) (q + s) (by omega)
        (castForm (by omega : k + l = (p + r) + (q + s)) (smoothWedge ω η))

def isPPFormTD (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [HasLocallyConstantCharts n X]
    (p : ℕ) (ω : SmoothForm n X (2 * p)) : Prop :=
  isPQForm n X p p (by rw [Nat.two_mul]) ω

-- isPPClass is defined in Hodge.Cohomology.Basic to avoid circular dependencies

variable {n : ℕ} {X : Type u}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]

theorem ofForm_wedge_TD {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l)
    (hω : IsFormClosed ω) (hη : IsFormClosed η) :
    ⟦ω ⋏ η, isFormClosed_wedge ω η hω hη⟧ = ⟦ω, hω⟧ * ⟦η, hη⟧ :=
  ofForm_wedge ω η hω hη

theorem two_add_two_mul (p : ℕ) : 2 + 2 * p = 2 * (p + 1) := by ring

/-- Powers of the Kähler form ω^p.

    **Implementation:**
    - ω^0 = 0 (placeholder; unit form lives in degree 0, but is stubbed elsewhere)
    - ω^1 = ω (the Kähler form)
    - ω^(p+2) = ω ∧ ω^(p+1) (with a degree cast using `castForm`)

    **Note**: This removes the previous degeneracy `kahlerPow p = 0` for `p ≥ 2`.
    `kahlerPow 0` is now the unit form (constant 1). -/
noncomputable def kahlerPow (p : ℕ) : SmoothForm n X (2 * p) :=
  match p with
  | 0 => unitForm  -- ω^0 = 1 (unit form)
  | 1 => (Nat.two_mul 1).symm ▸ K.omega_form  -- ω^1 = ω
  | p + 2 =>
      -- ω^(p+2) = ω ∧ ω^(p+1), with degree cast:
      -- deg(ω) = 2, deg(ω^(p+1)) = 2*(p+1), so deg = 2 + 2*(p+1) = 2*(p+2)
      castForm (two_add_two_mul (p + 1)) (K.omega_form ⋏ kahlerPow (p + 1))

theorem omega_pow_IsFormClosed (p : ℕ) : IsFormClosed (kahlerPow (n := n) (X := X) p) := by
  unfold kahlerPow
  match p with
  | 0 => exact isFormClosed_unitForm
  | 1 =>
    cases (Nat.two_mul 1).symm
    exact K.omega_closed
  | p + 2 =>
    -- cast preserves closedness
    -- (in the current stubbed setup, all forms are closed anyway, but we keep the structured proof)
    have hω : IsFormClosed (K.omega_form) := K.omega_closed
    have hp1 : IsFormClosed (kahlerPow (n := n) (X := X) (p + 1)) := omega_pow_IsFormClosed (p + 1)
    have hw : IsFormClosed (K.omega_form ⋏ kahlerPow (n := n) (X := X) (p + 1)) :=
      isFormClosed_wedge _ _ hω hp1
    -- `castForm` preserves closedness
    exact
      IsFormClosed_castForm (n := n) (X := X) (two_add_two_mul (p + 1))
        (K.omega_form ⋏ kahlerPow (n := n) (X := X) (p + 1)) hw

theorem omega_pow_is_rational_TD (p : ℕ) :
    isRationalClass ⟦kahlerPow (n := n) (X := X) p, omega_pow_IsFormClosed p⟧ := by
  unfold kahlerPow
  match p with
  | 0 =>
    -- ω^0 = unitForm, which is rational
    have h : ⟦unitForm, omega_pow_IsFormClosed (n := n) (X := X) 0⟧ = unitClass := by
      apply Quotient.sound
      exact cohomologous_refl _
    rw [h]
    exact isRationalClass_unit
  | 1 =>
    cases (Nat.two_mul 1).symm
    exact K.omega_rational
  | p + 2 =>
    -- ω^(p+2) = cast (ω ∧ ω^(p+1)); rationality follows from product of rationals
    have hω_closed : IsFormClosed (K.omega_form) := K.omega_closed
    have hp1_closed : IsFormClosed (kahlerPow (n := n) (X := X) (p + 1)) := omega_pow_IsFormClosed (p + 1)
    have hω_rat : isRationalClass ⟦K.omega_form, hω_closed⟧ := K.omega_rational
    have hp1_rat : isRationalClass ⟦kahlerPow (n := n) (X := X) (p + 1), hp1_closed⟧ :=
      omega_pow_is_rational_TD (p + 1)
    have hw_closed : IsFormClosed (K.omega_form ⋏ kahlerPow (n := n) (X := X) (p + 1)) :=
      isFormClosed_wedge _ _ hω_closed hp1_closed
    -- rationality of the wedge (product in cohomology)
    have hprod :
        isRationalClass (⟦K.omega_form, hω_closed⟧ * ⟦kahlerPow (n := n) (X := X) (p + 1), hp1_closed⟧) :=
      isRationalClass_mul _ _ hω_rat hp1_rat
    have hw_rat :
        isRationalClass (⟦K.omega_form ⋏ kahlerPow (n := n) (X := X) (p + 1), hw_closed⟧) := by
      simpa [ofForm_wedge] using hprod
    -- transport along the degree cast used in `kahlerPow`
    have hcast :=
      isRationalClass_cast (n := n) (X := X) (two_add_two_mul (p + 1))
        (⟦K.omega_form ⋏ kahlerPow (n := n) (X := X) (p + 1), hw_closed⟧) hw_rat
    -- rewrite casted class as the class of the casted representative (`kahlerPow (p+2)`)
    simpa [DeRhamCohomologyClass.cast_ofForm, IsFormClosed_castForm, castForm] using hcast
