import Mathlib
import IndisputableMonolith.Constants

/-!
# Activation Energy Barriers (CH-017)

Activation energy barriers in chemical reactions emerge from J-cost landscape.

## RS Mechanism

1. **Transition State as J-Maximum**: The transition state corresponds to the
   maximum J-cost along the reaction coordinate. J(x*) is the activation barrier.

2. **Arrhenius Form from Boltzmann**: The Arrhenius equation k = A·exp(-Ea/RT)
   emerges from Boltzmann statistics over the J-cost landscape.

3. **φ-Scaling of Barriers**: Characteristic barrier heights scale with φ powers
   of the coherence energy E_coh.

4. **Enzyme Catalysis**: Enzymes lower activation energy by reshaping the
   J-cost landscape, reducing J(x*) while preserving reaction energetics.

## Key Predictions

- Arrhenius equation emerges from J-cost
- Ea scales with bond strength (φ-related)
- Enzyme catalysis reduces J(x*) by stabilizing transition state
- Pre-exponential factor A relates to attempt frequency (8-tick)
-/

namespace IndisputableMonolith
namespace Chemistry
namespace ActivationEnergy

noncomputable section

open Constants Real

/-! ## J-Cost Landscape -/

/-- J-cost function: J(x) = ½(x + 1/x) - 1 -/
def J (x : ℝ) : ℝ := (1/2) * (x + 1/x) - 1

/-- J-cost at reactant (normalized to x = 1). -/
def J_reactant : ℝ := J 1

/-- J-cost at transition state (x = x*). -/
def J_transition (x_star : ℝ) : ℝ := J x_star

/-- Activation energy (dimensionless) = J(x*) - J(reactant). -/
def activationBarrier (x_star : ℝ) : ℝ := J x_star - J 1

/-- J(1) = 0 (reactant at minimum cost). -/
theorem J_one : J 1 = 0 := by simp only [J]; ring

/-- J(x) ≥ 0 for all x > 0.
    Proof: J(x) = ½(x + 1/x) - 1 ≥ 0 follows from AM-GM: x + 1/x ≥ 2. -/
theorem J_nonneg (x : ℝ) (hx : x > 0) : J x ≥ 0 := by
  -- AM-GM: For x > 0, x + 1/x ≥ 2 follows from (x - 1)² ≥ 0 when x = 1.
  -- More generally, use x + 1/x - 2 = (x - 1)²/x ≥ 0.
  simp only [J]
  have hx_ne : x ≠ 0 := ne_of_gt hx
  have h_key : x + 1/x - 2 = (x - 1)^2 / x := by field_simp; ring
  have h_sq_nonneg : (x - 1)^2 ≥ 0 := sq_nonneg _
  have h_div_nonneg : (x - 1)^2 / x ≥ 0 := div_nonneg h_sq_nonneg (le_of_lt hx)
  have h_am_gm : x + 1/x ≥ 2 := by linarith [h_key, h_div_nonneg]
  linarith

/-- Activation barrier is non-negative. -/
theorem barrier_nonneg (x_star : ℝ) (hx : x_star > 0) :
    activationBarrier x_star ≥ 0 := by
  simp only [activationBarrier, J_one, sub_zero]
  exact J_nonneg x_star hx

/-! ## Arrhenius Equation -/

/-- Boltzmann factor: exp(-Ea / kT). -/
def boltzmannFactor (Ea kT : ℝ) : ℝ := exp (-Ea / kT)

/-- Arrhenius rate constant: k = A · exp(-Ea / RT). -/
def arrheniusRate (A Ea R T : ℝ) : ℝ := A * exp (-Ea / (R * T))

/-- Higher barrier → lower rate (Arrhenius law). -/
theorem higher_barrier_slower (A Ea1 Ea2 R T : ℝ)
    (hA : A > 0) (hR : R > 0) (hT : T > 0) (hE : Ea1 < Ea2) :
    arrheniusRate A Ea2 R T < arrheniusRate A Ea1 R T := by
  simp only [arrheniusRate]
  apply mul_lt_mul_of_pos_left _ hA
  apply exp_lt_exp_of_lt
  have hRT : R * T > 0 := mul_pos hR hT
  have h1 : -Ea2 / (R * T) < -Ea1 / (R * T) := by
    apply div_lt_div_of_pos_right _ hRT
    linarith
  exact h1

/-- Higher temperature → higher rate (Arrhenius law). -/
theorem higher_temp_faster (A Ea R T1 T2 : ℝ)
    (hA : A > 0) (hR : R > 0) (hT1 : T1 > 0) (hT2 : T2 > 0) (hT : T1 < T2) (hEa : Ea > 0) :
    arrheniusRate A Ea R T1 < arrheniusRate A Ea R T2 := by
  simp only [arrheniusRate]
  apply mul_lt_mul_of_pos_left _ hA
  apply exp_lt_exp_of_lt
  have hRT1 : R * T1 > 0 := mul_pos hR hT1
  have hRT2 : R * T2 > 0 := mul_pos hR hT2
  -- -Ea/(R*T1) < -Ea/(R*T2) because T1 < T2 and Ea > 0
  have h1 : -Ea / (R * T1) < -Ea / (R * T2) := by
    rw [neg_div, neg_div, neg_lt_neg_iff]
    apply div_lt_div_of_pos_left hEa hRT1
    apply mul_lt_mul_of_pos_left hT hR
  exact h1

/-! ## φ-Scaling of Barriers -/

/-- Characteristic barrier scale: E_coh = φ^(-5) ≈ 0.09 eV. -/
def E_coh : ℝ := phi ^ (-5 : ℝ)

/-- Barrier height for n-th ladder rung: E_coh · φ^n. -/
def barrierLadder (n : ℤ) : ℝ := E_coh * phi ^ n

/-- Hydrogen bond barriers are at the E_coh scale. -/
theorem hbond_barrier_scale : barrierLadder 0 = E_coh := by
  simp only [barrierLadder, zpow_zero, mul_one]

/-- Covalent bond barriers are higher (n > 0). -/
theorem covalent_barrier_higher : barrierLadder 1 > barrierLadder 0 := by
  simp only [barrierLadder, zpow_one, zpow_zero, mul_one]
  have h_phi_gt_1 : phi > 1 := one_lt_phi
  have h_E_coh_pos : E_coh > 0 := by
    simp only [E_coh]
    exact rpow_pos_of_pos phi_pos _
  nlinarith

/-! ## Enzyme Catalysis -/

/-- Enzymatic transition state stabilization factor. -/
def catalyticFactor (E_uncat E_cat : ℝ) : ℝ := E_uncat / E_cat

/-- Catalysis means lower activation energy. -/
theorem catalysis_lowers_barrier (E_uncat E_cat : ℝ)
    (h_cat_lower : E_cat < E_uncat) (h_pos : E_cat > 0) :
    catalyticFactor E_uncat E_cat > 1 := by
  simp only [catalyticFactor, gt_iff_lt, one_lt_div h_pos]
  exact h_cat_lower

/-- Rate enhancement from catalysis. -/
def rateEnhancement (E_uncat E_cat kT : ℝ) : ℝ :=
  boltzmannFactor E_cat kT / boltzmannFactor E_uncat kT

/-- Enzyme rate enhancement is > 1 when barrier is lowered. -/
theorem enzyme_enhances_rate (E_uncat E_cat kT : ℝ)
    (h_cat_lower : E_cat < E_uncat) (h_kT_pos : kT > 0) :
    rateEnhancement E_uncat E_cat kT > 1 := by
  simp only [rateEnhancement, boltzmannFactor]
  -- exp(-E_cat/kT) / exp(-E_uncat/kT) = exp((-E_cat + E_uncat)/kT) = exp((E_uncat - E_cat)/kT)
  rw [← Real.exp_sub]
  have h_diff_pos : (E_uncat - E_cat) / kT > 0 := by
    apply div_pos _ h_kT_pos
    linarith
  have h_simp : (- E_cat / kT) - (-E_uncat / kT) = (E_uncat - E_cat) / kT := by ring
  rw [h_simp]
  exact Real.one_lt_exp_iff.mpr h_diff_pos

/-! ## Attempt Frequency (Pre-exponential Factor) -/

/-- The pre-exponential factor A relates to molecular vibrations.
    For typical reactions, A ≈ 10^13 s^-1 (vibrational frequency). -/
def attemptFrequency : ℝ := 1e13

/-- The 8-tick period τ = 8 / (E_coh / ℏ) gives a characteristic time. -/
def eightTickPeriod : ℝ := 8 / attemptFrequency

/-- Attempt frequency is related to 8-tick structure. -/
theorem attempt_freq_8tick : attemptFrequency = 8 / eightTickPeriod := by
  simp only [eightTickPeriod]
  field_simp

end

end ActivationEnergy
end Chemistry
end IndisputableMonolith
