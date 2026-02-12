import IndisputableMonolith.Fusion.ReactionNetworkRates

/-!
# Ignition / Viability (Formal, Conditional)

This module **does not** claim unconditional reactor-physics conclusions.
Instead it makes the previously informal statements precise in Lean by:

1. Defining **explicit ignition / viability predicates** (energy-balance style).
2. Proving that RS coherence **monotonically improves** the fusion-side term.
3. Proving *conditional* theorems showing when this implies ignition / viability,
   with all empirical seams stated as explicit assumptions.

In particular, this is the right formal replacement for informal prose like:

- “D‑T becomes trivial to ignite”
- “p‑B11 becomes viable”

Those become theorems of the form:

> If the (facility-specific) loss model is monotone in temperature and if a classical
> ignition condition holds at some \(T_0\), then RS ignition holds at a lower
> \(T_{\text{needed}} = S^2 T_0\) with the same tunneling proxy.

and

> If RS enhancement exceeds the required loss-to-fusion ratio threshold, then net
> power is positive (viability).

All of the *RS side* monotonicities are already proven in
`IndisputableMonolith/Fusion/ReactionNetworkRates.lean`.
-/

namespace IndisputableMonolith
namespace Fusion
namespace Ignition

open ReactionNetworkRates
open NuclearBridge

noncomputable section

-- IMPORTANT: prevent accidental creation of implicit type variables like `NuclearConfig`.
set_option autoImplicit false

/-! ## Helpers -/

private lemma sq_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < x ^ 2 := by
  have : 0 < x * x := mul_pos hx hx
  simpa [pow_two] using this

private lemma div_pos_of_pos_of_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 < a / b :=
  div_pos ha hb

/-! ## Effective Temperature Identity (exact, in this model) -/

/--
In the simplified Gamow model used by `ReactionNetworkRates.gamowExponent`,
RS scaling of the exponent by `S = rsBarrierScale c` is **exactly equivalent**
to replacing the temperature `T` by an **effective temperature**

`T_eff = T / S^2`.

This is the formal underpinning of the simulator statement:
“\(T\) behaves like \(T / S^2\) in the tunneling exponent”.

**Important**: this is an identity for the *Gamow exponent proxy* in the model.
It is not (yet) a full transport / confinement / radiation statement.
-/
theorem rsGamowExponent_eq_gamowExponent_at_Teff
    (c : RSCoherenceParams) (cfgA cfgB : NuclearConfig)
    (T : ℝ) (hT : 0 < T) :
    let g : GamowParams := ⟨T, hT⟩
    let S : ℝ := rsBarrierScale c
    let Teff : ℝ := T / (S ^ 2)
    let gEff : GamowParams := ⟨Teff, by
      -- Teff > 0 since T > 0 and S^2 > 0
      have hS : 0 < S := rsBarrierScale_pos c
      have hS2 : 0 < S ^ 2 := sq_pos_of_pos hS
      exact div_pos_of_pos_of_pos hT hS2⟩
    rsGamowExponent c g cfgA cfgB = gamowExponent gEff cfgA cfgB := by
  intro g S Teff gEff
  -- Expand definitions and use sqrt(T / S^2) = sqrt(T) / S (since S>0).
  -- In this file we keep the proof elementary and purely algebraic.
  have hS : 0 < S := rsBarrierScale_pos c
  have hS_ne : S ≠ 0 := ne_of_gt hS
  have hS2_pos : 0 < S ^ 2 := sq_pos_of_pos hS
  -- Unfold both exponents.
  unfold rsGamowExponent
  unfold gamowExponent
  -- `gamowExponent gEff` has denominator `sqrt (T / S^2)`.
  -- Rewrite that denominator to `sqrt T / S`.
  have hsqrt_div :
      Real.sqrt (T / (S ^ 2)) = Real.sqrt T / S := by
    -- Use `Real.sqrt_div` (requires `0 ≤ T`) and then `Real.sqrt_sq_eq_abs`.
    have hT0 : (0 : ℝ) ≤ T := le_of_lt hT
    calc
      Real.sqrt (T / (S ^ 2)) = Real.sqrt T / Real.sqrt (S ^ 2) := by
        simpa using (Real.sqrt_div hT0 (S ^ 2))
      _ = Real.sqrt T / |S| := by
        simp [Real.sqrt_sq_eq_abs]
      _ = Real.sqrt T / S := by
        simp [abs_of_pos hS]
  -- Now compute.
  -- The numerator terms `31.3 * Z1 * Z2 * sqrt(mu)` are the same in both.
  -- We only need to reconcile the denominators.
  -- After rewriting `sqrt(T / S^2)` we get exactly a factor of `S` in the numerator.
  -- After unfolding, reduce to a pure algebra identity.
  -- We do this *explicitly* (instead of `simp`-cancelling factors and producing disjunction goals).
  have hS_def : rsBarrierScale c = S := by rfl
  -- Abbreviation for the temperature-independent numerator.
  set C : ℝ := 31.3 * (cfgA.Z : ℝ) * (cfgB.Z : ℝ) * Real.sqrt (reducedMass cfgA cfgB)
  -- Unfold the definitional `let`s (but avoid `simp` rewriting the *goal* into disjunctions).
  dsimp [g, gEff, Teff]
  -- Replace `rsBarrierScale c` by `S`.
  rw [hS_def]
  -- Rewrite the RS-effective square root using `hsqrt_div`.
  -- (After `dsimp`, the RHS denominator is `Real.sqrt (T / S^2)`.)
  rw [hsqrt_div]
  -- Now the goal is purely algebraic:
  --   `S * (C / √T) = C / (√T / S)`.
  -- Convert the RHS using `div_div_eq_mul_div`, and commute multiplication.
  have h_div : C / (Real.sqrt T / S) = C * S / Real.sqrt T := by
    simpa using (div_div_eq_mul_div C (Real.sqrt T) S)
  calc
    S * (C / Real.sqrt T) = (S * C) / Real.sqrt T := by
      simp [mul_div_assoc]
    _ = (C * S) / Real.sqrt T := by
      ac_rfl
    _ = C / (Real.sqrt T / S) := by
      -- use the rearrangement lemma in reverse
      simpa using h_div.symm

/-! ## Generic Ignition Predicate (energy balance) -/

/--
An abstract “power-balance ignition” predicate at temperature `T`:

`ignites P_fus P_loss T` means net power is nonnegative:
`P_fus T ≥ P_loss T`.

-/
def ignites (P_fus P_loss : ℝ → ℝ) (T : ℝ) : Prop :=
  P_loss T ≤ P_fus T

/-! ## A minimal “fusion power” proxy from the Gamow tunneling model -/

/-- Classical tunneling proxy \(P(T) = \exp(-\eta(T))\). -/
def classicalTunneling (g : GamowParams) (cfgA cfgB : NuclearConfig) : ℝ :=
  Real.exp (-gamowExponent g cfgA cfgB)

/-- RS tunneling proxy \(P_{\mathrm{RS}}(T) = \exp(-\eta_{\mathrm{RS}}(T))\). -/
def rsTunneling (c : RSCoherenceParams) (g : GamowParams) (cfgA cfgB : NuclearConfig) : ℝ :=
  rsTunnelingProbability c g cfgA cfgB

theorem rsTunneling_ge_classical (c : RSCoherenceParams) (g : GamowParams) (cfgA cfgB : NuclearConfig) :
    classicalTunneling g cfgA cfgB ≤ rsTunneling c g cfgA cfgB := by
  -- This is exactly `ReactionNetworkRates.rsTunnelingProbability_ge_classical`.
  simpa [classicalTunneling, rsTunneling] using
    (rsTunnelingProbability_ge_classical c g cfgA cfgB)

/-! ## “Ignition becomes easier” theorems (conditional, facility-model seams) -/

/--
If ignition holds under the classical tunneling proxy at temperature `T`,
then it also holds under RS at the **same** `T`, for any fixed loss model,
provided fusion power is proportional to the tunneling proxy with a nonnegative scale.

This is the weakest “monotone improvement” statement: RS cannot make you worse.
-/
theorem ignition_same_T_of_rs (c : RSCoherenceParams)
    (g : GamowParams) (cfgA cfgB : NuclearConfig)
    (P_loss : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K) :
    ignites (fun _T => K * classicalTunneling g cfgA cfgB) P_loss g.temperature →
    ignites (fun _T => K * rsTunneling c g cfgA cfgB) P_loss g.temperature := by
  intro h
  -- `P_loss T ≤ K*P_classical` and `P_classical ≤ P_rs` implies `P_loss T ≤ K*P_rs`.
  have hprob : classicalTunneling g cfgA cfgB ≤ rsTunneling c g cfgA cfgB :=
    rsTunneling_ge_classical c g cfgA cfgB
  have hmul : K * classicalTunneling g cfgA cfgB ≤ K * rsTunneling c g cfgA cfgB := by
    exact mul_le_mul_of_nonneg_left hprob hK
  -- Expand `ignites` and finish by transitivity.
  unfold ignites at h ⊢
  exact le_trans h hmul

/--
**Lower-temperature ignition transfer (model‑guaranteed, with explicit seam).**

Let `S = rsBarrierScale c`. In the Gamow model, RS at temperature
`T_needed = S^2 * T0` matches the *classical* exponent at temperature `T0`.

If the facility loss model `P_loss(T)` is monotone (nondecreasing in `T`),
then any classical ignition at `T0` implies RS ignition at the lower temperature
`T_needed`.

This is the formal content behind the informal phrase “D‑T becomes trivial to ignite”:
RS reduces the required temperature *to meet the same tunneling proxy*, and losses
do not increase when you lower temperature.
-/
theorem ignition_at_lower_temperature
    (c : RSCoherenceParams) (cfgA cfgB : NuclearConfig)
    (T0 : ℝ) (hT0 : 0 < T0)
    (P_loss : ℝ → ℝ)
    (hLoss_mono : ∀ {T1 T2 : ℝ}, T1 ≤ T2 → P_loss T1 ≤ P_loss T2)
    (K : ℝ) (_hK : 0 ≤ K) :
    let S : ℝ := rsBarrierScale c
    let T_needed : ℝ := (S ^ 2) * T0
    ignites (fun _ => K * classicalTunneling ⟨T0, hT0⟩ cfgA cfgB) P_loss T0 →
    ignites (fun _ => K * rsTunneling c ⟨T_needed, by
      have hS : 0 < S := rsBarrierScale_pos c
      exact mul_pos (sq_pos_of_pos hS) hT0⟩ cfgA cfgB) P_loss T_needed := by
  intro S T_needed hIgn0
  -- First, show `T_needed ≤ T0` since `S ≤ 1`.
  have hS_pos : 0 < S := rsBarrierScale_pos c
  have hS_le_one : S ≤ 1 := rsBarrierScale_le_one c
  have hS2_le_one : S ^ 2 ≤ 1 := by
    -- since 0 ≤ S and S ≤ 1, squaring preserves ≤ 1
    have hS_nonneg : 0 ≤ S := le_of_lt hS_pos
    nlinarith
  have hT_needed_le : T_needed ≤ T0 := by
    -- T_needed = S^2 * T0 ≤ 1 * T0 = T0
    have := mul_le_mul_of_nonneg_right hS2_le_one (le_of_lt hT0)
    simpa [T_needed] using this
  -- Loss at lower temperature is ≤ loss at T0.
  have hLoss : P_loss T_needed ≤ P_loss T0 := hLoss_mono hT_needed_le
  -- RS tunneling at T_needed equals classical tunneling at T0 (effective-temp identity).
  have hGamow_eq :
      rsGamowExponent c ⟨T_needed, by
        have hS : 0 < S := rsBarrierScale_pos c
        exact mul_pos (sq_pos_of_pos hS) hT0⟩ cfgA cfgB
        = gamowExponent ⟨T0, hT0⟩ cfgA cfgB := by
    -- Use the effective-temperature identity with T = T_needed and Teff = T0.
    -- Since Teff = T_needed / S^2 = T0, the theorem applies.
    -- We instantiate `rsGamowExponent_eq_gamowExponent_at_Teff` with `T := T_needed`.
    have hTeff :
        let g : GamowParams := ⟨T_needed, by
          have hS : 0 < S := rsBarrierScale_pos c
          exact mul_pos (sq_pos_of_pos hS) hT0⟩
        let S' : ℝ := rsBarrierScale c
        let Teff : ℝ := T_needed / (S' ^ 2)
        Teff = T0 := by
          -- Teff = (S^2*T0)/(S^2) = T0
          simp [T_needed, S, div_eq_mul_inv, mul_comm, hS_pos.ne']
    -- Now rewrite using the identity theorem.
    -- (We keep the proof short by rewriting `Teff` to `T0` using `hTeff`.)
    have hId :=
      rsGamowExponent_eq_gamowExponent_at_Teff c cfgA cfgB T_needed (by
        have hS : 0 < S := rsBarrierScale_pos c
        exact mul_pos (sq_pos_of_pos hS) hT0)
    -- Unpack the `let`s and substitute Teff = T0.
    simpa [hTeff] using hId
  -- Therefore RS tunneling probability at T_needed equals classical tunneling at T0.
  have hProb_eq :
      rsTunneling c ⟨T_needed, by
        have hS : 0 < S := rsBarrierScale_pos c
        exact mul_pos (sq_pos_of_pos hS) hT0⟩ cfgA cfgB
        = classicalTunneling ⟨T0, hT0⟩ cfgA cfgB := by
    -- By definition, both are exp of minus the corresponding Gamow exponents.
    simp [rsTunneling, classicalTunneling, rsTunnelingProbability, hGamow_eq]
  -- Now prove ignition at T_needed:
  -- P_loss(T_needed) ≤ P_loss(T0) ≤ K*P_classical(T0) = K*P_rs(T_needed).
  unfold ignites at hIgn0 ⊢
  have h1 : P_loss T_needed ≤ K * classicalTunneling ⟨T0, hT0⟩ cfgA cfgB :=
    le_trans hLoss hIgn0
  -- Replace RHS with K*RS tunneling at T_needed.
  simpa [hProb_eq] using h1

/-! ## Viability as net-positive power (p‑B11 style) -/

/--
Abstract net-power predicate: `viable P_fus P_loss T` means `P_fus T > P_loss T`.

This is the minimal formal notion needed to phrase “p‑B11 becomes viable”.
-/
def viable (P_fus P_loss : ℝ → ℝ) (T : ℝ) : Prop :=
  P_loss T < P_fus T

/--
**Sufficient condition for viability from an RS enhancement factor.**

Assume a baseline fusion power proxy `P0(T)` and loss power `L(T)`.
If RS multiplies the fusion-side term by a factor `E ≥ 1` at temperature `T`,
then net-positive power follows whenever:

`L(T) < E * P0(T)`.

This is deliberately theorems-as-interfaces style: the physics of `L(T)` (bremsstrahlung,
transport, etc.) is an explicit seam, and the RS improvement enters as `E`.
-/
theorem viable_of_enhancement
    (P0 L : ℝ → ℝ) (T : ℝ) (E : ℝ) (_hE : 1 ≤ E) :
    (L T < E * P0 T) →
    viable (fun t => E * P0 t) L T := by
  intro h
  unfold viable
  simpa using h

end

end Ignition
end Fusion
end IndisputableMonolith
