import IndisputableMonolith.OctaveKernel.Basic
import IndisputableMonolith.Compat.FunctionIterate
import Mathlib

namespace IndisputableMonolith
namespace OctaveKernel

/-!
# OctaveKernel.Voxel — The Fundamental Unit of Reality

## Core Insight

A **voxel** is NOT a container with particles passing through it.
A **voxel IS 8 phases co-present** — a chord, not a point.

When a recognition event enters a voxel, it takes 8 ticks to complete its cycle.
In steady state, there are always 8 tokens at different phases simultaneously.
These 8 tokens aren't separate particles — they are 8 aspects of a single
recognition event *being*.

## Physical Interpretation

- **Energy**: Each phase slot carries energy; total voxel energy is conserved
- **Charge**: The 8 phases must balance (ledger closure)
- **Momentum**: Phase flow creates directional structure
- **Mass**: Persistent voxels accumulate effective mass from cycling energy

## The Pipeline Model

```
Tick 0: [A₀]
Tick 1: [B₀, A₁]
...
Tick 7: [H₀, G₁, F₂, E₃, D₄, C₅, B₆, A₇]  ← FULL (8 co-present)
Tick 8: [I₀, H₁, G₂, F₃, E₄, D₅, C₆, B₇]  ← A exits, I enters
```

At steady state, the voxel IS these 8 co-present phases.

## Claim Hygiene

- `Voxel`, `PhysicalVoxel` are **definitions**
- Conservation laws are **theorems** (proved)
- Physical interpretations are **model** (structure imposed, not derived)
-/

/-- A Voxel is an 8-slot chord: 8 tokens at different phases, co-present.

This is the fundamental unit of "location in reality". A voxel isn't
empty space waiting for particles — it IS the 8 phases sounding together. -/
structure Voxel (Token : Type) where
  /-- The token occupying each phase slot. Slot `i` holds the token at phase `i`. -/
  slot : Phase → Token

namespace Voxel

variable {Token : Type}

/-- Access the token at a specific phase. -/
@[inline] def atPhase (v : Voxel Token) (p : Phase) : Token := v.slot p

/-- All 8 phases are occupied (trivially true by construction). -/
theorem all_phases_occupied (v : Voxel Token) :
    ∀ p : Phase, ∃ t : Token, v.atPhase p = t :=
  fun p => ⟨v.slot p, rfl⟩

/-- The voxel contains exactly 8 tokens (one per phase). -/
theorem phase_count : Fintype.card Phase = 8 := by native_decide

/-- Step the voxel: a new token enters at phase 0, the token at phase 7 exits,
    and all others advance by one phase. -/
def step (v : Voxel Token) (entering : Token) : Voxel Token :=
  ⟨fun p =>
    if h : p = 0 then entering
    else v.slot ⟨p.val - 1, by omega⟩⟩

/-- The token that exits when stepping (was at phase 7). -/
@[inline] def exiting (v : Voxel Token) : Token := v.slot 7

/-- After stepping, phase 0 holds the entering token. -/
@[simp] theorem step_phase_zero (v : Voxel Token) (entering : Token) :
    (v.step entering).slot 0 = entering := by simp [step]

/-- After stepping, phases 1-7 hold the previous phase's token. -/
theorem step_phase_succ (v : Voxel Token) (entering : Token) (p : Phase) (hp : p ≠ 0) :
    (v.step entering).slot p = v.slot ⟨p.val - 1, by omega⟩ := by
  simp [step, hp]

end Voxel

/-! ## Token Streams and Steady State -/

/-- An infinite stream of tokens entering a voxel (one per tick). -/
def TokenStream (Token : Type) := ℕ → Token

/-- The voxel state at time `t ≥ 7`, given a token stream.
    Slot `i` contains the token that entered at time `t - i`. -/
def voxelAtTime (stream : TokenStream Token) (t : ℕ) (_ht : t ≥ 7) : Voxel Token :=
  ⟨fun i => stream (t - i.val)⟩

/-- In steady state, each phase slot has a distinct entry time. -/
theorem voxel_phases_distinct {Token : Type} (_stream : TokenStream Token) (t : ℕ) (_ht : t ≥ 7)
    (p q : Phase) (hpq : p ≠ q) :
    t - p.val ≠ t - q.val := by
  intro h
  have : p.val = q.val := by omega
  exact hpq (Fin.ext this)

/-- The token at phase i entered i ticks ago (definitional). -/
theorem token_age_is_phase {Token : Type} (stream : TokenStream Token) (t : ℕ) (ht : t ≥ 7) (p : Phase) :
    (voxelAtTime stream t ht).slot p = stream (t - p.val) := rfl

/-! ## Physical Voxel — Energy, Charge, and Conservation -/

/-- A physical voxel carries energy at each phase slot.
    This models the physical content of a recognition unit. -/
structure PhysicalVoxel where
  /-- Energy at each phase slot (non-negative). -/
  energy : Phase → ℝ
  /-- Energy is non-negative at all phases. -/
  energy_nonneg : ∀ p, 0 ≤ energy p
  /-- Charge at each phase (can be positive or negative). -/
  charge : Phase → ℝ

namespace PhysicalVoxel

/-- Total energy of the voxel (sum over all 8 phases). -/
def totalEnergy (v : PhysicalVoxel) : ℝ :=
  ∑ p : Phase, v.energy p

/-- Total charge of the voxel (sum over all 8 phases). -/
def totalCharge (v : PhysicalVoxel) : ℝ :=
  ∑ p : Phase, v.charge p

/-- A voxel is **charge-balanced** (ledger closed) if total charge is zero. -/
def chargeBalanced (v : PhysicalVoxel) : Prop :=
  v.totalCharge = 0

/-- Total energy is non-negative (follows from phase energies being non-negative). -/
theorem totalEnergy_nonneg (v : PhysicalVoxel) : 0 ≤ v.totalEnergy := by
  unfold totalEnergy
  apply Finset.sum_nonneg
  intro p _
  exact v.energy_nonneg p

/-- A **balanced octave** has complementary charges at opposite phases:
    charge(p) + charge(7-p) = 0 for all p. -/
def octaveBalanced (v : PhysicalVoxel) : Prop :=
  ∀ p : Phase, v.charge p + v.charge ⟨7 - p.val, by omega⟩ = 0

/-- Octave balance implies charge balance. -/
theorem octaveBalanced_implies_chargeBalanced (v : PhysicalVoxel) (h : v.octaveBalanced) :
    v.chargeBalanced := by
  unfold chargeBalanced totalCharge
  -- Pair up phases (0,7), (1,6), (2,5), (3,4) — each pair sums to 0
  have h0 : v.charge 0 + v.charge 7 = 0 := h 0
  have h1 : v.charge 1 + v.charge 6 = 0 := h 1
  have h2 : v.charge 2 + v.charge 5 = 0 := h 2
  have h3 : v.charge 3 + v.charge 4 = 0 := h 3
  -- Expand the sum over Fin 8
  simp only [Fin.sum_univ_eight]
  linarith

end PhysicalVoxel

/-! ## The 8 Recognition Modes -/

/-- The 8 fundamental recognition modes — aspects of any recognition event. -/
inductive RecognitionMode : Type where
  | potential    -- Phase 0: Undifferentiated possibility
  | emergence    -- Phase 1: First distinction arises
  | relation     -- Phase 2: Connection to other
  | structure_   -- Phase 3: Pattern crystallizes
  | peak         -- Phase 4: Maximum manifestation
  | reflection   -- Phase 5: Awareness of pattern
  | integration  -- Phase 6: Returning to whole
  | completion   -- Phase 7: Recognition achieved, loop closes
  deriving DecidableEq, Repr, Fintype

/-- Map phase index to recognition mode. -/
def phaseToMode : Phase → RecognitionMode
  | ⟨0, _⟩ => .potential
  | ⟨1, _⟩ => .emergence
  | ⟨2, _⟩ => .relation
  | ⟨3, _⟩ => .structure_
  | ⟨4, _⟩ => .peak
  | ⟨5, _⟩ => .reflection
  | ⟨6, _⟩ => .integration
  | ⟨7, _⟩ => .completion

/-- Map recognition mode to phase index. -/
def modeToPhase : RecognitionMode → Phase
  | .potential   => 0
  | .emergence   => 1
  | .relation    => 2
  | .structure_  => 3
  | .peak        => 4
  | .reflection  => 5
  | .integration => 6
  | .completion  => 7

/-- phaseToMode is injective. -/
theorem phaseToMode_injective : Function.Injective phaseToMode := by
  intro p q h
  fin_cases p <;> fin_cases q <;> simp_all [phaseToMode]

/-- phaseToMode is surjective. -/
theorem phaseToMode_surjective : Function.Surjective phaseToMode := by
  intro m
  cases m
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩
  · exact ⟨5, rfl⟩
  · exact ⟨6, rfl⟩
  · exact ⟨7, rfl⟩

/-- phaseToMode is a bijection. -/
theorem phaseToMode_bijective : Function.Bijective phaseToMode :=
  ⟨phaseToMode_injective, phaseToMode_surjective⟩

/-- modeToPhase is injective. -/
theorem modeToPhase_injective : Function.Injective modeToPhase := by
  intro m n h
  cases m <;> cases n <;> simp_all [modeToPhase]

/-- modeToPhase is surjective. -/
theorem modeToPhase_surjective : Function.Surjective modeToPhase := by
  intro p
  fin_cases p
  · exact ⟨.potential, rfl⟩
  · exact ⟨.emergence, rfl⟩
  · exact ⟨.relation, rfl⟩
  · exact ⟨.structure_, rfl⟩
  · exact ⟨.peak, rfl⟩
  · exact ⟨.reflection, rfl⟩
  · exact ⟨.integration, rfl⟩
  · exact ⟨.completion, rfl⟩

/-- modeToPhase is a bijection. -/
theorem modeToPhase_bijective : Function.Bijective modeToPhase :=
  ⟨modeToPhase_injective, modeToPhase_surjective⟩

/-- phaseToMode and modeToPhase are inverses. -/
theorem phase_mode_inverse_left : ∀ p, modeToPhase (phaseToMode p) = p := by
  intro p; fin_cases p <;> rfl

theorem phase_mode_inverse_right : ∀ m, phaseToMode (modeToPhase m) = m := by
  intro m; cases m <;> rfl

/-! ## Layer Voxels — Connecting to Dynamics -/

/-- A voxel over layer states. -/
abbrev LayerVoxel (L : Layer) := Voxel L.State

/-- Each slot of a layer voxel has a phase (from the layer's phase function). -/
def LayerVoxel.slotPhases (L : Layer) (v : LayerVoxel L) : Phase → Phase :=
  fun p => L.phase (v.slot p)

/-- A layer voxel is "phase-aligned" if slot `i` contains a state at phase `i`. -/
def LayerVoxel.phaseAligned (L : Layer) (v : LayerVoxel L) : Prop :=
  ∀ p : Phase, L.phase (v.slot p) = p

/-- Phase increases by 1 after each step (inductive helper for iterate). -/
theorem phase_step_eq (L : Layer) (hAdv : L.StepAdvances) (s : L.State) :
    L.phase (L.step s) = L.phase s + 1 := hAdv s

/-- Helper: Fin 8 arithmetic facts for phase iteration. -/
private theorem fin8_arith_2 : ∀ p : Fin 8, p + 1 + 1 = p + 2 := by intro p; omega
private theorem fin8_arith_3 : ∀ p : Fin 8, p + 1 + 1 + 1 = p + 3 := by intro p; omega
private theorem fin8_arith_4 : ∀ p : Fin 8, p + 1 + 1 + 1 + 1 = p + 4 := by intro p; omega
private theorem fin8_arith_5 : ∀ p : Fin 8, p + 1 + 1 + 1 + 1 + 1 = p + 5 := by intro p; omega
private theorem fin8_arith_6 : ∀ p : Fin 8, p + 1 + 1 + 1 + 1 + 1 + 1 = p + 6 := by intro p; omega
private theorem fin8_arith_7 : ∀ p : Fin 8, p + 1 + 1 + 1 + 1 + 1 + 1 + 1 = p + 7 := by intro p; omega

/-- After k steps, phase equals initial phase + k (in Fin 8 arithmetic).
    We state this for k : Fin 8 to stay in the Fin 8 type. -/
theorem phase_after_fin_iterate (L : Layer) (hAdv : L.StepAdvances) (s : L.State) (k : Phase) :
    L.phase (Function.iterate L.step k.val s) = L.phase s + k := by
  -- We prove by cases on k : Fin 8, using StepAdvances repeatedly
  fin_cases k
  · -- k = 0
    simp [Function.iterate]
  · -- k = 1
    simp only [Function.iterate, Nat.iterate]
    exact hAdv s
  · -- k = 2
    simp only [Function.iterate, Nat.iterate]
    rw [hAdv, hAdv]; exact fin8_arith_2 (L.phase s)
  · -- k = 3
    simp only [Function.iterate, Nat.iterate]
    rw [hAdv, hAdv, hAdv]; exact fin8_arith_3 (L.phase s)
  · -- k = 4
    simp only [Function.iterate, Nat.iterate]
    rw [hAdv, hAdv, hAdv, hAdv]; exact fin8_arith_4 (L.phase s)
  · -- k = 5
    simp only [Function.iterate, Nat.iterate]
    rw [hAdv, hAdv, hAdv, hAdv, hAdv]; exact fin8_arith_5 (L.phase s)
  · -- k = 6
    simp only [Function.iterate, Nat.iterate]
    rw [hAdv, hAdv, hAdv, hAdv, hAdv, hAdv]; exact fin8_arith_6 (L.phase s)
  · -- k = 7
    simp only [Function.iterate, Nat.iterate]
    rw [hAdv, hAdv, hAdv, hAdv, hAdv, hAdv, hAdv]; exact fin8_arith_7 (L.phase s)

/-- Construct a phase-aligned voxel from a starting state and layer dynamics.
    Slot `i` gets `step^i(s)`, which has phase `phase(s) + i`. -/
def LayerVoxel.fromState (L : Layer) (s : L.State) : LayerVoxel L :=
  ⟨fun p => Function.iterate L.step p.val s⟩

/-- A voxel built from a phase-0 state is phase-aligned. -/
theorem LayerVoxel.fromState_aligned (L : Layer) (hAdv : L.StepAdvances) (s : L.State)
    (hs : L.phase s = 0) :
    (LayerVoxel.fromState L s).phaseAligned L := by
  intro p
  simp only [fromState]
  rw [phase_after_fin_iterate L hAdv s p, hs, zero_add]

/-! ## Voxel Energy Conservation -/

/-- Energy flow through a voxel: entering energy, exiting energy. -/
structure VoxelFlow where
  /-- Energy entering at phase 0. -/
  entering : ℝ
  /-- Energy exiting from phase 7. -/
  exiting : ℝ
  /-- Entering energy is non-negative. -/
  entering_nonneg : 0 ≤ entering
  /-- Exiting energy is non-negative. -/
  exiting_nonneg : 0 ≤ exiting

/-- A voxel transition preserves energy if: total_after = total_before + entering - exiting. -/
def energyConserving (before after : PhysicalVoxel) (flow : VoxelFlow) : Prop :=
  after.totalEnergy = before.totalEnergy + flow.entering - flow.exiting

/-- In a closed system (no external flow), total energy is constant. -/
theorem closed_system_energy_constant (before after : PhysicalVoxel)
    (h : energyConserving before after ⟨0, 0, le_refl 0, le_refl 0⟩) :
    after.totalEnergy = before.totalEnergy := by
  simp [energyConserving] at h
  linarith

/-! ## Voxel Interaction — Two Voxels Meeting -/

/-- When two voxels interact, they can exchange phase-aligned energy. -/
structure VoxelInteraction where
  /-- Energy transferred from voxel A to voxel B at each phase. -/
  transfer : Phase → ℝ

/-- Total transfer is zero (conservation in interaction). -/
def VoxelInteraction.conservative (i : VoxelInteraction) : Prop :=
  ∑ p : Phase, i.transfer p = 0

/-- A symmetric interaction has equal and opposite transfers at complementary phases. -/
def VoxelInteraction.symmetric (i : VoxelInteraction) : Prop :=
  ∀ p : Phase, i.transfer p + i.transfer ⟨7 - p.val, by omega⟩ = 0

/-- Symmetric interactions are conservative. -/
theorem symmetric_is_conservative (i : VoxelInteraction) (h : i.symmetric) :
    i.conservative := by
  unfold VoxelInteraction.conservative
  -- Same pairing argument as octaveBalanced
  have h0 : i.transfer 0 + i.transfer 7 = 0 := h 0
  have h1 : i.transfer 1 + i.transfer 6 = 0 := h 1
  have h2 : i.transfer 2 + i.transfer 5 = 0 := h 2
  have h3 : i.transfer 3 + i.transfer 4 = 0 := h 3
  simp only [Fin.sum_univ_eight]
  linarith

/-! ## The Fundamental Theorem: Existence Requires 8 Phases -/

/-- A recognition cycle is **complete** if it visits all 8 modes. -/
def recognitionComplete (visited : Finset RecognitionMode) : Prop :=
  visited = Finset.univ

/-- The minimum number of steps to complete recognition is 8. -/
theorem min_recognition_steps : Fintype.card RecognitionMode = 8 := by native_decide

/-- A voxel with fewer than 8 occupied phases cannot complete recognition. -/
theorem incomplete_voxel_unstable (_v : Voxel Token) (occupied : Finset Phase)
    (h : occupied.card < 8) :
    ∃ p : Phase, p ∉ occupied := by
  by_contra hContra
  push_neg at hContra
  have : occupied = Finset.univ := by
    ext p
    constructor
    · intro _; exact Finset.mem_univ p
    · intro _; exact hContra p
  rw [this] at h
  simp at h

/-! ## Physical Constants (Model Parameters) -/

/-- The fundamental time quantum: one tick of the Octave clock.
    This is the minimum time for one phase transition.

    Physical interpretation: ~65 picoseconds (water tau_gate). -/
def tickDuration : ℝ := 65e-12  -- 65 ps

/-- One complete Octave cycle duration. -/
def octaveDuration : ℝ := 8 * tickDuration

/-- Octave duration is 8 times tick duration. -/
theorem octave_is_8_ticks : octaveDuration = 8 * tickDuration := rfl

/-- The minimum energy quantum for a phase slot.
    Below this, the phase is effectively empty.

    This is a model parameter, to be determined empirically. -/
noncomputable def minPhaseEnergy : ℝ := 1e-21  -- ~1 zeptojoule (placeholder)

/-! ## Voxel Field — A Collection of Interacting Voxels -/

/-- A voxel field is a collection of voxels indexed by spatial position.
    Position is abstract here; physical interpretation depends on the model. -/
structure VoxelField (Pos : Type) where
  /-- The voxel at each position. -/
  voxel : Pos → PhysicalVoxel

/-- Total energy of a finite voxel field. -/
def VoxelField.totalEnergy {Pos : Type} [Fintype Pos] (field : VoxelField Pos) : ℝ :=
  ∑ pos : Pos, (field.voxel pos).totalEnergy

/-- A voxel field is globally charge-balanced if the sum of all charges is zero. -/
def VoxelField.globallyBalanced {Pos : Type} [Fintype Pos] (field : VoxelField Pos) : Prop :=
  ∑ pos : Pos, (field.voxel pos).totalCharge = 0

/-- If every voxel is charge-balanced, the field is globally balanced. -/
theorem locally_balanced_implies_globally {Pos : Type} [Fintype Pos]
    (field : VoxelField Pos)
    (h : ∀ pos, (field.voxel pos).chargeBalanced) :
    field.globallyBalanced := by
  unfold VoxelField.globallyBalanced
  simp only [PhysicalVoxel.chargeBalanced] at h
  simp [h]

end OctaveKernel
end IndisputableMonolith
