import IndisputableMonolith.Fusion.Ignition

/-!
# Concrete Power-Balance Models (Loss + Deposition) for Fusion

This module provides **concrete, checkable** functions

- `L(T,n,Zeff,τE,...)`  (loss power)
- `P0(T,n,...)`        (baseline fusion heating proxy)

and proves the structural hypotheses needed by the formal ignition / viability theorems
in `IndisputableMonolith/Fusion/Ignition.lean`.

## What is and is not claimed

These are **model-layer** functions, not an assertion that nature must follow them.
They are introduced so that national-lab runs can supply:

1. a chosen loss model `L(...)` (e.g. bremsstrahlung + transport),
2. a chosen fusion heating proxy `P0(...)` (e.g. density² × tunneling proxy × Q),
3. and then formally prove that the hypotheses in the ignition/viability theorems
   are satisfied for the chosen model.

In particular:

- We **prove** monotonicity-in-temperature properties for these formulas.
- We **do not** hardcode facility-specific calibration constants here.
  Coefficients are explicit parameters with nonnegativity constraints.

This preserves rigor: theorems are clear about what is derived vs what is a seam.
-/

namespace IndisputableMonolith
namespace Fusion
namespace PowerBalance

open ReactionNetworkRates
open Ignition
open NuclearBridge

noncomputable section

set_option autoImplicit false

/-! ## Parameters -/

/-- Nonnegative real parameter bundle for the loss/heating models. -/
structure Params where
  -- Bremsstrahlung coefficient (units absorbed into RS-native scaling).
  k_brem : ℝ
  k_brem_nonneg : 0 ≤ k_brem
  -- Transport coefficient (e.g. 3/2 · 1/τE, in suitable units).
  k_tr : ℝ
  k_tr_nonneg : 0 ≤ k_tr
  -- Fusion-heating coefficient (absorbs Q-value, geometry, etc.).
  k_fus : ℝ
  k_fus_nonneg : 0 ≤ k_fus
  -- Deposition fraction in [0,1] (alpha deposition etc.).
  f_dep : ℝ
  f_dep_nonneg : 0 ≤ f_dep
  f_dep_le_one : f_dep ≤ 1

/-! ## Loss model L(T,n,Zeff) = brems + transport -/

/--
Bremsstrahlung power loss proxy (Tokamak-like, fully ionized):

`L_brem(T,n,Zeff) = k_brem · Zeff · n^2 · √T`

This is monotone nondecreasing in `T` for `T ≥ 0` when the parameters are nonnegative.
-/
def L_brem (P : Params) (T n Zeff : ℝ) : ℝ :=
  P.k_brem * Zeff * (n ^ 2) * Real.sqrt T

/--
Transport / conduction power loss proxy:

`L_tr(T,n) = k_tr · n · T`

This is monotone nondecreasing in `T` when `k_tr ≥ 0` and `n ≥ 0`.
-/
def L_tr (P : Params) (T n : ℝ) : ℝ :=
  P.k_tr * n * T

/-- Total loss proxy: `L = L_brem + L_tr`. -/
def L_total (P : Params) (T n Zeff : ℝ) : ℝ :=
  L_brem P T n Zeff + L_tr P T n

/-! ## Fusion heating proxy P0(T,n) = k_fus · n^2 · exp(-η(T)) -/

/--
Baseline fusion heating proxy (before RS enhancement):

`P0(T,n) = k_fus · n^2 · classicalTunneling(g(T), cfgA, cfgB)`

Here `classicalTunneling` is the Lean-defined proxy `exp(-η(T))`
from `Fusion.Ignition`.
-/
def P0 (P : Params) (g : GamowParams) (cfgA cfgB : NuclearConfig) (n : ℝ) : ℝ :=
  P.k_fus * (n ^ 2) * classicalTunneling g cfgA cfgB

/--
Deposited fusion heating proxy:

`Pdep0(T,n) = f_dep · P0(T,n)`

(This is what actually heats the plasma; the remainder escapes as neutrons, radiation, etc.)
-/
def Pdep0 (P : Params) (g : GamowParams) (cfgA cfgB : NuclearConfig) (n : ℝ) : ℝ :=
  P.f_dep * P0 P g cfgA cfgB n

/-! ## Monotonicity results (discharging `hLoss_mono`) -/

private lemma sqrt_monotone : Monotone Real.sqrt := Real.sqrt_monotone

theorem L_brem_monotone_T (P : Params) (n Zeff : ℝ)
    (hZ : 0 ≤ Zeff) :
    Monotone (fun T => L_brem P T n Zeff) := by
  intro T1 T2 hT
  unfold L_brem
  -- Everything is a nonnegative scalar times `sqrt T`, which is monotone.
  have hk : 0 ≤ P.k_brem * Zeff * (n ^ 2) := by
    have hn2 : 0 ≤ n ^ 2 := by nlinarith
    have : 0 ≤ P.k_brem * Zeff := mul_nonneg P.k_brem_nonneg hZ
    exact mul_nonneg this hn2
  have hs : Real.sqrt T1 ≤ Real.sqrt T2 := sqrt_monotone hT
  -- Multiply the monotone part by a nonnegative constant.
  nlinarith

theorem L_tr_monotone_T (P : Params) (n : ℝ) (hn : 0 ≤ n) :
    Monotone (fun T => L_tr P T n) := by
  intro T1 T2 hT
  unfold L_tr
  have hk : 0 ≤ P.k_tr * n := mul_nonneg P.k_tr_nonneg hn
  -- linear in T with nonnegative slope
  nlinarith

theorem L_total_monotone_T (P : Params) (n Zeff : ℝ)
    (hn : 0 ≤ n) (hZ : 0 ≤ Zeff) :
    Monotone (fun T => L_total P T n Zeff) := by
  intro T1 T2 hT
  unfold L_total
  have h1 := L_brem_monotone_T P n Zeff hZ hT
  have h2 := L_tr_monotone_T P n hn hT
  linarith

/-! ## Net-power and the inequality form needed for viability -/

/--
Net power proxy (deposited fusion heating minus losses):

`net0(T) = Pdep0(T,n) - L_total(T,n,Zeff)`.
-/
def net0 (P : Params) (g : GamowParams) (cfgA cfgB : NuclearConfig) (n Zeff : ℝ) : ℝ :=
  Pdep0 P g cfgA cfgB n - L_total P g.temperature n Zeff

/--
RS enhancement factor in the tunneling proxy:

`E = rsTunneling / classicalTunneling`

This is ≥ 1 (proved from `rsTunnelingProbability_ge_classical`).
-/
def enhancement (c : RSCoherenceParams) (g : GamowParams) (cfgA cfgB : NuclearConfig) : ℝ :=
  rsTunneling c g cfgA cfgB / classicalTunneling g cfgA cfgB

theorem classicalTunneling_pos (g : GamowParams) (cfgA cfgB : NuclearConfig) :
    0 < classicalTunneling g cfgA cfgB := by
  -- exp(x) is always positive
  unfold classicalTunneling
  exact Real.exp_pos _

theorem enhancement_ge_one (c : RSCoherenceParams) (g : GamowParams) (cfgA cfgB : NuclearConfig) :
    1 ≤ enhancement c g cfgA cfgB := by
  have hpos : 0 < classicalTunneling g cfgA cfgB := classicalTunneling_pos g cfgA cfgB
  have hle : classicalTunneling g cfgA cfgB ≤ rsTunneling c g cfgA cfgB :=
    rsTunneling_ge_classical (c := c) (g := g) (cfgA := cfgA) (cfgB := cfgB)
  -- divide both sides by a nonnegative number (in fact positive)
  have hnonneg : 0 ≤ classicalTunneling g cfgA cfgB := le_of_lt hpos
  have hdiv : classicalTunneling g cfgA cfgB / classicalTunneling g cfgA cfgB ≤
      rsTunneling c g cfgA cfgB / classicalTunneling g cfgA cfgB :=
    div_le_div_of_nonneg_right hle hnonneg
  -- rewrite `classical/classical = 1` and recognize `enhancement`
  have h1 : classicalTunneling g cfgA cfgB / classicalTunneling g cfgA cfgB = (1 : ℝ) := by
    simp [div_self, hpos.ne']
  -- finish
  simpa [enhancement, h1] using hdiv

/--
Concrete instantiation of `Ignition.viable_of_enhancement` using `L_total` and `P0`.

This turns “p‑B11 becomes viable” into a checkable inequality:
`L_total(T,n,Zeff) < E · Pdep0(T,n)`.
-/
theorem viable_of_enhancement_concrete
    (P : Params) (g : GamowParams) (cfgA cfgB : NuclearConfig)
    (T : ℝ) (n Zeff : ℝ) (E : ℝ) (hE : 1 ≤ E) :
    (L_total P T n Zeff < E * Pdep0 P g cfgA cfgB n) →
    viable (fun _ => E * Pdep0 P g cfgA cfgB n) (fun _ => L_total P T n Zeff) T := by
  intro h
  -- This is exactly `Ignition.viable_of_enhancement` specialized.
  simpa [Ignition.viable] using (Ignition.viable_of_enhancement (P0 := fun _ => Pdep0 P g cfgA cfgB n)
    (L := fun _ => L_total P T n Zeff) (T := T) (E := E) hE h)

end

end PowerBalance
end Fusion
end IndisputableMonolith
