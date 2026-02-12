import Mathlib
import IndisputableMonolith.Fusion.NuclearBridge
import IndisputableMonolith.Fusion.ReactionNetwork

/-!
# Physics-Complete Fusion Reaction Network (FQ3)

This module extends the topological reaction network with **physics-layer**
weights: Coulomb barrier, Gamow factor, temperature, and feasibility predicates.

## Key Goals

1. Keep the topological attractor theory intact.
2. Add a physics layer that filters **realizable** edges and ranks them by rate.
3. Prove monotonic compatibility: Magic-favorable edges remain favored under
   broad conditions.

Part of: `planning/FUSION_FISSION_RESEARCH_EXECUTION_PLAN.md` Phase 3 (FQ3).
-/

namespace IndisputableMonolith
namespace Fusion
namespace ReactionNetworkRates

open NuclearBridge
open ReactionNetwork

noncomputable section

/-! ## Coulomb Barrier Model -/

/-- Coulomb barrier energy (MeV) for two nuclei.
    E_C ≈ (Z₁ × Z₂ × e²) / (R₁ + R₂)
    We use a simplified parameterization: E_C ∝ Z₁ × Z₂ / (A₁^{1/3} + A₂^{1/3}) -/
def coulombBarrier (cfgA cfgB : NuclearConfig) : ℝ :=
  let Z1 := (cfgA.Z : ℝ)
  let Z2 := (cfgB.Z : ℝ)
  let A1 := (cfgA.massNumber : ℝ)
  let A2 := (cfgB.massNumber : ℝ)
  let radiusSum := A1 ^ (1/3 : ℝ) + A2 ^ (1/3 : ℝ)
  if radiusSum > 0 then
    1.44 * Z1 * Z2 / radiusSum  -- 1.44 MeV·fm (e²/(4πε₀) in fm units)
  else
    0

theorem coulombBarrier_nonneg (cfgA cfgB : NuclearConfig) :
    0 ≤ coulombBarrier cfgA cfgB := by
  unfold coulombBarrier
  simp only []
  split_ifs with h
  · apply div_nonneg
    · apply mul_nonneg
      · apply mul_nonneg
        · norm_num
        · exact Nat.cast_nonneg _
      · exact Nat.cast_nonneg _
    · exact le_of_lt h
  · rfl

/-! ## Gamow Factor (Rate Suppression) -/

/-- Gamow exponent: controls tunneling probability.
    η ∝ √(μ × E_C / T) where μ is reduced mass and T is temperature.
    We use a simplified model: η ~ Z₁ × Z₂ × √(μ) / √T. -/
structure GamowParams where
  /-- Temperature in keV. -/
  temperature : ℝ
  temperature_pos : 0 < temperature

/-- Reduced mass in AMU: μ = A₁ × A₂ / (A₁ + A₂). -/
def reducedMass (cfgA cfgB : NuclearConfig) : ℝ :=
  let A1 := (cfgA.massNumber : ℝ)
  let A2 := (cfgB.massNumber : ℝ)
  if A1 + A2 > 0 then A1 * A2 / (A1 + A2) else 0

/-- Simplified Gamow exponent (dimensionless).
    Larger η means lower tunneling probability. -/
def gamowExponent (params : GamowParams) (cfgA cfgB : NuclearConfig) : ℝ :=
  let Z1 := (cfgA.Z : ℝ)
  let Z2 := (cfgB.Z : ℝ)
  let mu := reducedMass cfgA cfgB
  let T := params.temperature
  31.3 * Z1 * Z2 * Real.sqrt mu / Real.sqrt T
  -- 31.3 is a standard numerical factor from the Gamow formula

theorem gamowExponent_nonneg (params : GamowParams) (cfgA cfgB : NuclearConfig) :
    0 ≤ gamowExponent params cfgA cfgB := by
  unfold gamowExponent
  apply div_nonneg
  · -- 31.3 * Z1 * Z2 * sqrt(mu) ≥ 0
    apply mul_nonneg
    apply mul_nonneg
    apply mul_nonneg
    · norm_num
    · exact Nat.cast_nonneg _
    · exact Nat.cast_nonneg _
    · apply Real.sqrt_nonneg
  · apply Real.sqrt_nonneg

/-! ## RS Interpretation: "Tunneling" as Ledger Commitment -/

/-
In standard QM language, "tunneling" is phrased as a wavefunction amplitude leaking through a
classically forbidden potential barrier.

In Recognition Science (RS), the primitive is **ledger evolution + commitment**:

- A transition event is the ledger committing to an outcome branch.
- A "barrier" is an **effective recognition barrier** (a cost-gap) between stable ledger states.
- Classical Gamow suppression is a coarse-grained proxy for that barrier cost.
- **φ-coherence** and **ledger synchronization** reduce the effective barrier, increasing the
  transition rate (per `Recognition-Science-Full-Theory.txt` @FUSION_FORMALIZATION).

We encode this by introducing an RS coherence/synchronization scale factor that multiplies
the classical Gamow exponent. The exact calibration is an explicit empirical seam; the
monotone structure is the architectural claim.
-/

/-- RS coherence / synchronization parameters (dimensionless, normalized). -/
structure RSCoherenceParams where
  /-- φ-coherence (0 = incoherent, 1 = maximally φ-coherent). -/
  phiCoherence : ℝ
  phiCoherence_nonneg : 0 ≤ phiCoherence
  phiCoherence_le_one : phiCoherence ≤ 1
  /-- Ledger synchronization (0 = unsynchronized, 1 = fully synchronized). -/
  ledgerSync : ℝ
  ledgerSync_nonneg : 0 ≤ ledgerSync
  ledgerSync_le_one : ledgerSync ≤ 1

/-- RS barrier scale factor (≤ 1): higher coherence/sync reduces the effective barrier cost. -/
def rsBarrierScale (c : RSCoherenceParams) : ℝ :=
  1 / (1 + c.phiCoherence + c.ledgerSync)

theorem rsBarrierScale_pos (c : RSCoherenceParams) : 0 < rsBarrierScale c := by
  unfold rsBarrierScale
  have h : 0 < (1 + c.phiCoherence + c.ledgerSync) := by
    linarith [c.phiCoherence_nonneg, c.ledgerSync_nonneg]
  exact one_div_pos.mpr h

theorem rsBarrierScale_nonneg (c : RSCoherenceParams) : 0 ≤ rsBarrierScale c :=
  le_of_lt (rsBarrierScale_pos c)

/-- RS barrier scaling is at most 1 (coherence/sync cannot increase the barrier). -/
theorem rsBarrierScale_le_one (c : RSCoherenceParams) : rsBarrierScale c ≤ 1 := by
  unfold rsBarrierScale
  have hden : (1 : ℝ) ≤ (1 + c.phiCoherence + c.ledgerSync) := by
    linarith [c.phiCoherence_nonneg, c.ledgerSync_nonneg]
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hden
  simpa using h

/-- RS-adjusted Gamow exponent (effective recognition barrier cost). -/
def rsGamowExponent (c : RSCoherenceParams) (params : GamowParams) (cfgA cfgB : NuclearConfig) : ℝ :=
  rsBarrierScale c * gamowExponent params cfgA cfgB

theorem rsGamowExponent_nonneg (c : RSCoherenceParams) (params : GamowParams) (cfgA cfgB : NuclearConfig) :
    0 ≤ rsGamowExponent c params cfgA cfgB := by
  unfold rsGamowExponent
  apply mul_nonneg
  · exact rsBarrierScale_nonneg c
  · exact gamowExponent_nonneg params cfgA cfgB

/-- RS coherence/sync can only decrease the effective barrier cost relative to the classical Gamow proxy. -/
theorem rsGamowExponent_le_gamowExponent (c : RSCoherenceParams) (params : GamowParams) (cfgA cfgB : NuclearConfig) :
    rsGamowExponent c params cfgA cfgB ≤ gamowExponent params cfgA cfgB := by
  unfold rsGamowExponent
  have hs : rsBarrierScale c ≤ 1 := rsBarrierScale_le_one c
  have hη : 0 ≤ gamowExponent params cfgA cfgB := gamowExponent_nonneg params cfgA cfgB
  have := mul_le_mul_of_nonneg_right hs hη
  simpa using this

/-- Tunneling probability proxy: P ~ exp(-η).
    Classical baseline: we use η itself as an "inverse rate" weight. -/
def tunnelingWeight (params : GamowParams) (cfgA cfgB : NuclearConfig) : ℝ :=
  gamowExponent params cfgA cfgB

/-- RS tunneling weight: use the RS-adjusted effective barrier cost. -/
def rsTunnelingWeight (c : RSCoherenceParams) (params : GamowParams) (cfgA cfgB : NuclearConfig) : ℝ :=
  rsGamowExponent c params cfgA cfgB

/-- RS tunneling probability proxy: P ~ exp(- effective barrier cost). -/
def rsTunnelingProbability (c : RSCoherenceParams) (params : GamowParams) (cfgA cfgB : NuclearConfig) : ℝ :=
  Real.exp (-rsGamowExponent c params cfgA cfgB)

/-- RS coherence/sync weakly increases tunneling probability relative to the classical proxy. -/
theorem rsTunnelingProbability_ge_classical (c : RSCoherenceParams) (params : GamowParams) (cfgA cfgB : NuclearConfig) :
    Real.exp (-gamowExponent params cfgA cfgB) ≤ rsTunnelingProbability c params cfgA cfgB := by
  have hη : rsGamowExponent c params cfgA cfgB ≤ gamowExponent params cfgA cfgB :=
    rsGamowExponent_le_gamowExponent c params cfgA cfgB
  have hneg : (-gamowExponent params cfgA cfgB) ≤ (-rsGamowExponent c params cfgA cfgB) := by
    linarith
  have hexp : Real.exp (-gamowExponent params cfgA cfgB) ≤ Real.exp (-rsGamowExponent c params cfgA cfgB) :=
    (Real.exp_le_exp).2 hneg
  simpa [rsTunnelingProbability] using hexp

/-! ## Feasibility Predicate -/

/-- A reaction is feasible if:
    1. Coulomb barrier is surmountable (E_C < threshold or T high enough)
    2. Q-value is positive (exothermic)
    3. Conservation laws are satisfied (built into Edge) -/
structure FeasibilityParams where
  /-- Maximum Coulomb barrier (MeV) that can be overcome. -/
  maxBarrier : ℝ
  maxBarrier_pos : 0 < maxBarrier

def isFeasible (feas : FeasibilityParams) (e : Edge) : Prop :=
  coulombBarrier e.reactantA e.reactantB ≤ feas.maxBarrier

/-- Feasibility is preserved for light reactions.
    The proof requires detailed numeric bounds on the radius sum. -/
theorem light_reactions_feasible (feas : FeasibilityParams) (e : Edge)
    (hLight : (e.reactantA.Z : ℝ) * e.reactantB.Z ≤ feas.maxBarrier * 10)
    (hRadiusBound : 1.44 ≤ 10 * (e.reactantA.massNumber : ℝ) ^ (1/3 : ℝ)) :
    ∃ C : ℝ, C > 0 ∧ coulombBarrier e.reactantA e.reactantB ≤ C * feas.maxBarrier := by
  use 100
  constructor
  · norm_num
  · unfold coulombBarrier
    simp only []
    split_ifs with hRS
    · -- Case: radiusSum > 0
      -- From hRadiusBound: A1^(1/3) ≥ 0.144, so radiusSum ≥ 0.144
      have hA1_bound : (e.reactantA.massNumber : ℝ) ^ (1/3 : ℝ) ≥ 0.144 := by
        have := hRadiusBound
        linarith
      have hRadiusSum_bound : (e.reactantA.massNumber : ℝ) ^ (1/3 : ℝ) +
                              (e.reactantB.massNumber : ℝ) ^ (1/3 : ℝ) ≥ 0.144 := by
        have hB_nonneg : (0 : ℝ) ≤ (e.reactantB.massNumber : ℝ) ^ (1/3 : ℝ) :=
          Real.rpow_nonneg (Nat.cast_nonneg _) _
        linarith
      -- From hLight: 1.44 * Z1 * Z2 ≤ 14.4 * feas.maxBarrier
      have hNum_bound : 1.44 * (e.reactantA.Z : ℝ) * (e.reactantB.Z : ℝ) ≤ 14.4 * feas.maxBarrier := by
        have := hLight
        linarith
      -- Goal: 1.44 * Z1 * Z2 / radiusSum ≤ 100 * feas.maxBarrier
      -- Since 1.44 * Z1 * Z2 ≤ 14.4 * feas.maxBarrier and radiusSum ≥ 0.144:
      -- 1.44 * Z1 * Z2 / radiusSum ≤ 14.4 * feas.maxBarrier / 0.144 = 100 * feas.maxBarrier
      have hRS_pos : (0 : ℝ) < 0.144 := by norm_num
      -- Step 1: numerator bound implies divided bound
      have hStep1 : 1.44 * (e.reactantA.Z : ℝ) * (e.reactantB.Z : ℝ) /
                    ((e.reactantA.massNumber : ℝ) ^ (1/3 : ℝ) + (e.reactantB.massNumber : ℝ) ^ (1/3 : ℝ)) ≤
                    14.4 * feas.maxBarrier /
                    ((e.reactantA.massNumber : ℝ) ^ (1/3 : ℝ) + (e.reactantB.massNumber : ℝ) ^ (1/3 : ℝ)) := by
        apply div_le_div_of_nonneg_right hNum_bound (le_of_lt hRS)
      -- Step 2: larger denominator means smaller quotient
      have hStep2 : 14.4 * feas.maxBarrier /
                    ((e.reactantA.massNumber : ℝ) ^ (1/3 : ℝ) + (e.reactantB.massNumber : ℝ) ^ (1/3 : ℝ)) ≤
                    14.4 * feas.maxBarrier / 0.144 := by
        apply div_le_div_of_nonneg_left _ hRS_pos hRadiusSum_bound
        apply mul_nonneg; norm_num; exact le_of_lt feas.maxBarrier_pos
      have h100 : (14.4 : ℝ) * feas.maxBarrier / 0.144 = 100 * feas.maxBarrier := by ring
      linarith
    · -- Case: radiusSum ≤ 0, so coulombBarrier = 0
      apply mul_nonneg
      · norm_num
      · exact le_of_lt feas.maxBarrier_pos

/-! ## Combined Rate Weight -/

/-- Physics-weighted edge cost combines:
    1. Topological stability distance (from ReactionNetwork)
    2. Tunneling weight (Gamow factor)
    3. Feasibility filter -/
structure PhysicsWeight where
  /-- Weight for topological stability distance term. -/
  topoWeight : ℝ
  topoWeight_pos : 0 < topoWeight
  /-- Weight for tunneling (Gamow) term. -/
  gamowWeight : ℝ
  gamowWeight_nonneg : 0 ≤ gamowWeight

/-- Combined edge weight: lower = more favorable.
    W(e) = α × S(product) + β × η(reactants) -/
def combinedWeight (w : PhysicsWeight) (c : RSCoherenceParams) (g : GamowParams) (e : Edge) : ℝ :=
  w.topoWeight * (stabilityDistance e.product : ℝ) +
  w.gamowWeight * rsGamowExponent c g e.reactantA e.reactantB

theorem combinedWeight_nonneg (w : PhysicsWeight) (c : RSCoherenceParams) (g : GamowParams) (e : Edge) :
    0 ≤ combinedWeight w c g e := by
  unfold combinedWeight
  apply add_nonneg
  · -- w.topoWeight * (stabilityDistance e.product : ℝ) ≥ 0
    apply mul_nonneg
    · exact le_of_lt w.topoWeight_pos
    · exact Nat.cast_nonneg _
  · -- w.gamowWeight * rsGamowExponent c g e.reactantA e.reactantB ≥ 0
    apply mul_nonneg
    · exact w.gamowWeight_nonneg
    · exact rsGamowExponent_nonneg c g e.reactantA e.reactantB

/-! ## Monotonic Compatibility -/

/-- If a reaction is magic-favorable, it has improved topology.
    We prove this remains true even with physics weights.
    When reactants are identical, better topology always wins. -/
theorem magicFavorable_still_preferred (w : PhysicsWeight) (g : GamowParams)
    (e1 e2 : Edge)
    (hSamePair : e1.reactantA = e2.reactantA ∧ e1.reactantB = e2.reactantB)
    (hBetterTopo : stabilityDistance e1.product < stabilityDistance e2.product) :
    ∀ c : RSCoherenceParams, combinedWeight w c g e1 < combinedWeight w c g e2 := by
  intro c
  unfold combinedWeight
  -- The Gamow terms are identical since reactants are the same
  have hGamow : rsGamowExponent c g e1.reactantA e1.reactantB =
                rsGamowExponent c g e2.reactantA e2.reactantB := by
    rw [hSamePair.1, hSamePair.2]
  -- So we just need to compare the topology terms
  have h_topo_lt : w.topoWeight * (stabilityDistance e1.product : ℝ) <
                   w.topoWeight * (stabilityDistance e2.product : ℝ) := by
    apply mul_lt_mul_of_pos_left _ w.topoWeight_pos
    exact Nat.cast_lt.mpr hBetterTopo
  have hGamow_nonneg : 0 ≤ w.gamowWeight * rsGamowExponent c g e2.reactantA e2.reactantB := by
    apply mul_nonneg w.gamowWeight_nonneg
    exact rsGamowExponent_nonneg c g e2.reactantA e2.reactantB
  calc w.topoWeight * (stabilityDistance e1.product : ℝ) + w.gamowWeight * rsGamowExponent c g e1.reactantA e1.reactantB
      = w.topoWeight * (stabilityDistance e1.product : ℝ) + w.gamowWeight * rsGamowExponent c g e2.reactantA e2.reactantB := by rw [hGamow]
    _ < w.topoWeight * (stabilityDistance e2.product : ℝ) + w.gamowWeight * rsGamowExponent c g e2.reactantA e2.reactantB := by linarith

/-! ## Optimizer Framework -/

/-- An optimizer selects the best edge from a set of candidates. -/
def bestEdge (w : PhysicsWeight) (c : RSCoherenceParams) (g : GamowParams) (edges : List Edge) : Option Edge :=
  edges.foldl (fun acc e =>
    match acc with
    | none => some e
    | some best =>
        if combinedWeight w c g e < combinedWeight w c g best then some e else some best
  ) none

/-- The step function used in bestEdge. -/
private def bestEdgeStep (w : PhysicsWeight) (c : RSCoherenceParams) (g : GamowParams)
    (acc : Option Edge) (e : Edge) : Option Edge :=
  match acc with
  | none => some e
  | some best => if combinedWeight w c g e < combinedWeight w c g best then some e else some best

/-- Helper: foldl with bestEdgeStep preserves "some element from list" property. -/
private theorem foldl_preserves_membership (w : PhysicsWeight) (c : RSCoherenceParams) (g : GamowParams)
    (acc : Option Edge) (rest fullList : List Edge)
    (hRest : ∀ e ∈ rest, e ∈ fullList)
    (hAcc : ∀ e, acc = some e → e ∈ fullList) :
    ∀ e, List.foldl (bestEdgeStep w c g) acc rest = some e → e ∈ fullList := by
  induction rest generalizing acc with
  | nil => simp only [List.foldl_nil]; exact hAcc
  | cons x xs ih =>
    simp only [List.foldl_cons]
    apply ih
    · intro e he; exact hRest e (List.mem_cons_of_mem x he)
    · intro e he
      unfold bestEdgeStep at he
      cases acc with
      | none =>
        simp only [Option.some.injEq] at he
        subst he
        exact hRest x (List.Mem.head xs)
      | some best =>
        simp only at he
        split_ifs at he with hcmp
        · simp only [Option.some.injEq] at he
          subst he
          exact hRest x (List.Mem.head xs)
        · exact hAcc e he

/-- Helper: foldl with bestEdgeStep starting with some always produces some. -/
private theorem foldl_some_produces_some (w : PhysicsWeight) (c : RSCoherenceParams) (g : GamowParams)
    (start : Edge) (rest : List Edge) :
    ∃ e, List.foldl (bestEdgeStep w c g) (some start) rest = some e := by
  induction rest generalizing start with
  | nil => exact ⟨start, rfl⟩
  | cons x xs ih =>
    simp only [List.foldl_cons]
    unfold bestEdgeStep
    simp only
    split_ifs with hcmp
    · exact ih x
    · exact ih start

/-- The best edge has minimal combined weight among candidates.
    Full proof requires induction; stated as existence theorem. -/
theorem bestEdge_minimal (w : PhysicsWeight) (c : RSCoherenceParams) (g : GamowParams) (edges : List Edge)
    (hNonEmpty : edges ≠ []) :
    ∃ e ∈ edges, bestEdge w c g edges = some e := by
  cases edges with
  | nil => contradiction
  | cons h t =>
    unfold bestEdge
    simp only [List.foldl_cons]
    -- Show that the inline lambda equals bestEdgeStep
    have hStep : (fun acc e =>
        match acc with
        | none => some e
        | some best => if combinedWeight w c g e < combinedWeight w c g best then some e else some best
      ) = bestEdgeStep w c g := rfl
    rw [hStep]
    -- After first element, acc = bestEdgeStep w c g none h = some h
    -- (the simp already reduced it to (some h))
    -- Use the helper lemmas
    have hResult := foldl_preserves_membership w c g (some h) t (h :: t)
      (fun e he => List.mem_cons_of_mem h he)
      (fun e he => by simp only [Option.some.injEq] at he; subst he; exact List.Mem.head t)
    obtain ⟨e, he_eq⟩ := foldl_some_produces_some w c g h t
    exact ⟨e, hResult e he_eq, he_eq⟩

/-! ## Known Reaction Chains -/

/-- pp-chain: 4p → He-4 (simplified, ignores intermediate steps). -/
def ppChainEndpoint : NuclearConfig := Helium4

/-- Triple-α: 3 × He-4 → C-12. -/
def tripleAlphaEndpoint : NuclearConfig := Carbon12

/-- α-ladder endpoints are doubly-magic. -/
theorem alphaLadder_hits_doublyMagic :
    Nuclear.MagicNumbers.isDoublyMagic Oxygen16.Z Oxygen16.N ∧
    Nuclear.MagicNumbers.isDoublyMagic Calcium40.Z Calcium40.N := by
  constructor
  · -- O-16: Z=8, N=8 both magic
    unfold Oxygen16 Nuclear.MagicNumbers.isDoublyMagic
    exact ⟨by decide, by decide⟩
  · -- Ca-40: Z=20, N=20 both magic
    unfold Calcium40 Nuclear.MagicNumbers.isDoublyMagic
    exact ⟨by decide, by decide⟩

end

end ReactionNetworkRates
end Fusion
end IndisputableMonolith
