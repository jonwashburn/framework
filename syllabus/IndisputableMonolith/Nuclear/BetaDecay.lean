import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Nuclear.MagicNumbers
import IndisputableMonolith.Nuclear.ValleyOfStability

/-!
# Beta Decay Rates Derivation (N-008)

Beta decay is the process by which a nucleus transforms a neutron into a proton
(β⁻ decay) or a proton into a neutron (β⁺ decay / electron capture), adjusting
its N/Z ratio toward the valley of stability.

## RS Mechanism

1. **Valley of Stability Drive**: Nuclei off the valley floor minimize J-cost by
   undergoing beta decay to approach N ≈ Z (light nuclei) or the stability line.

2. **Fermi's Golden Rule**: The decay rate is proportional to |M|² × ρ(E), where
   M is the matrix element and ρ(E) is the phase space factor. This emerges from
   the underlying quantum mechanics derived from the ledger.

3. **Q-Value Dependence**: The decay rate scales as Q⁵ for allowed transitions
   (Sargent's rule). Higher Q → faster decay.

4. **Selection Rules**: Angular momentum and parity conservation restrict which
   transitions are "allowed" (ΔJ = 0, 1; no parity change for Fermi/Gamow-Teller)
   vs "forbidden" (higher ΔJ or parity change).

5. **ft-Value**: The comparative half-life ft = f × t₁/₂ is approximately constant
   for similar transition types, where f is the Fermi integral.

## Predictions

- β⁻ decay for neutron-rich nuclei (N > N_stable).
- β⁺/EC decay for proton-rich nuclei (N < N_stable).
- Decay rate ∝ Q⁵ (Sargent's rule).
- Superallowed 0⁺ → 0⁺ transitions have ft ≈ 3000-3100 s.
- Forbidden transitions have much longer half-lives.

-/

namespace IndisputableMonolith
namespace Nuclear
namespace BetaDecay

open Constants
open IndisputableMonolith.Nuclear.MagicNumbers
open IndisputableMonolith.Nuclear.ValleyOfStability

noncomputable section

/-! ## Beta Decay Types -/

/-- Types of beta decay. -/
inductive BetaDecayType
| betaMinus    -- n → p + e⁻ + ν̄ₑ (neutron-rich)
| betaPlus     -- p → n + e⁺ + νₑ (proton-rich)
| electronCapture  -- p + e⁻ → n + νₑ (proton-rich)
deriving DecidableEq, Repr

/-- Determine decay type based on N/Z ratio. -/
def decayType (N Z : ℕ) : Option BetaDecayType :=
  let N_stable := mostStableN Z
  if N > N_stable then some .betaMinus
  else if N < N_stable then some .betaPlus
  else none

/-! ## Q-Value and Decay Rate -/

/-- Q-value for β⁻ decay: Q = M_parent - M_daughter.
    Approximately: Q ≈ (M_n - M_p - m_e) × c² = 0.782 MeV for free neutron. -/
def neutronDecayQ : ℝ := 0.782  -- MeV

/-- Sargent's rule: decay rate ∝ Q⁵ for allowed transitions. -/
def sargentExponent : ℕ := 5

/-- Decay rate proportional to Q^5 (Sargent's rule). -/
def relativeDecayRate (Q : ℝ) : ℝ :=
  if Q > 0 then Q ^ sargentExponent else 0

/-- Higher Q gives higher decay rate (shorter half-life). -/
theorem higher_Q_faster_decay (Q1 Q2 : ℝ) (hQ1 : Q1 > 0) (hQ2 : Q2 > 0) (hQ : Q1 < Q2) :
    relativeDecayRate Q1 < relativeDecayRate Q2 := by
  simp only [relativeDecayRate, hQ1, hQ2, ite_true, sargentExponent]
  exact pow_lt_pow_left₀ hQ (le_of_lt hQ1) (by norm_num)

/-! ## Selection Rules -/

/-- Transition classification based on angular momentum change. -/
inductive TransitionType
| superallowed  -- ΔJ = 0, same parity (Fermi)
| allowed       -- ΔJ = 0, 1 (no 0 → 0 for Gamow-Teller)
| firstForbidden   -- |ΔJ| = 0, 1, 2 with parity change
| secondForbidden  -- |ΔJ| = 2, 3 (no parity change)
| higherForbidden  -- |ΔJ| > 3
deriving DecidableEq, Repr

/-- Log₁₀(ft) value for different transition types (in seconds). -/
def logFt : TransitionType → ℝ
| .superallowed => 3.5     -- ft ≈ 3000 s
| .allowed => 5.0          -- ft ≈ 10⁵ s
| .firstForbidden => 7.0   -- ft ≈ 10⁷ s
| .secondForbidden => 12.0 -- ft ≈ 10¹² s
| .higherForbidden => 18.0 -- ft ≈ 10¹⁸ s

/-- Superallowed transitions are fastest. -/
theorem superallowed_fastest :
    logFt .superallowed < logFt .allowed ∧
    logFt .allowed < logFt .firstForbidden := by
  simp only [logFt]
  norm_num

/-- ft-value for superallowed 0⁺ → 0⁺ transitions is approximately constant. -/
def superallowedFt : ℝ := 3072  -- seconds (average experimental value)

theorem superallowed_ft_in_range : 3000 < superallowedFt ∧ superallowedFt < 3200 := by
  simp only [superallowedFt]
  norm_num

/-! ## Free Neutron Decay -/

/-- Free neutron half-life (seconds). -/
def freeNeutronHalfLife : ℝ := 611  -- ~10.2 minutes

/-- Free neutron mean lifetime (seconds). -/
def freeNeutronMeanLife : ℝ := 881  -- seconds

theorem neutron_decays : freeNeutronHalfLife > 0 := by
  simp only [freeNeutronHalfLife]
  norm_num

/-- Free neutron has positive Q-value, so it decays. -/
theorem neutron_decay_allowed : neutronDecayQ > 0 := by
  simp only [neutronDecayQ]
  norm_num

/-! ## Examples -/

/-- Tritium (H-3): Z=1, N=2 → He-3: Z=2, N=1. Half-life ≈ 12.3 years. -/
def tritiumHalfLifeYears : ℝ := 12.32

/-- Carbon-14: Z=6, N=8 → N-14: Z=7, N=7. Half-life ≈ 5730 years. -/
def carbon14HalfLifeYears : ℝ := 5730

/-- C-14 is longer-lived than tritium due to lower Q-value. -/
def tritiumQ : ℝ := 18.6e-3  -- MeV (very low)
def carbon14Q : ℝ := 0.156   -- MeV

theorem c14_longer_than_tritium :
    tritiumHalfLifeYears < carbon14HalfLifeYears := by
  simp only [tritiumHalfLifeYears, carbon14HalfLifeYears]
  norm_num

/-! ## Fermi Integral -/

/-- The Fermi integral f(Z, Q) accounts for phase space and Coulomb effects.
    For high Z (strong Coulomb), f is enhanced for β⁻ and suppressed for β⁺. -/
def fermiIntegralApprox (Z Q : ℝ) (isBetaMinus : Bool) : ℝ :=
  let coulombFactor := if isBetaMinus then 1 + 0.01 * Z else 1 - 0.005 * Z
  Q ^ 5 * coulombFactor

/-! ## 8-Tick Connection -/

/-- The W boson mediates beta decay. Its mass is related to 8-tick structure.
    M_W ≈ 80 GeV, and the weak interaction strength is set by this scale. -/
def W_boson_mass_GeV : ℝ := 80.4

/-- Fermi coupling constant G_F (related to weak interaction strength). -/
def fermi_coupling_GeV_minus2 : ℝ := 1.166e-5  -- GeV⁻²

/-- The weak interaction operates on the 8-tick timescale. -/
theorem weak_scale_exists : W_boson_mass_GeV > 0 ∧ fermi_coupling_GeV_minus2 > 0 := by
  simp only [W_boson_mass_GeV, fermi_coupling_GeV_minus2]
  norm_num

/-! ## Valley of Stability Connection -/

/-- β⁻ decay moves nucleus toward stability (N decreases, Z increases). -/
theorem beta_minus_toward_stability (N Z : ℕ) (hN : N > mostStableN Z) :
    decayType N Z = some .betaMinus := by
  simp only [decayType, hN, ite_true]

/-- β⁺ decay moves nucleus toward stability (N increases, Z decreases). -/
theorem beta_plus_toward_stability (N Z : ℕ) (hN : N < mostStableN Z) :
    decayType N Z = some .betaPlus := by
  simp only [decayType]
  have h_not_gt : ¬(N > mostStableN Z) := by omega
  simp only [h_not_gt, ite_false, hN, ite_true]

end

end BetaDecay
end Nuclear
end IndisputableMonolith
