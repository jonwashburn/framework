import IndisputableMonolith.OctaveKernel.VoxelMeaning
import IndisputableMonolith.OctaveKernel.Voxel
import IndisputableMonolith.Consciousness.GlobalPhase
import IndisputableMonolith.Foundation.RecognitionOperator
import Mathlib

/-!
# VoxelField — Collections of Voxels and Their Dynamics

This module formalizes how collections of voxels (MeaningfulVoxels) evolve
under the Recognition Operator R̂ and connect to Θ-dynamics.
-/

namespace IndisputableMonolith
namespace OctaveKernel

open Consciousness
open Foundation
open ProteinFolding.DFT8

/-! ## VoxelField Structure (M1.1) -/

structure MeaningfulVoxelField (Pos : Type) where
  voxel : Pos → MeaningfulVoxel

namespace MeaningfulVoxelField

variable {Pos : Type}

def photonAt (field : MeaningfulVoxelField Pos) (p : Pos) (k : Phase) : Photon :=
  (field.voxel p).photon k

noncomputable def spectrumAt (field : MeaningfulVoxelField Pos) (p : Pos) : Fin 8 → ℂ :=
  (field.voxel p).frequencySpectrum

noncomputable def modeAmplitudeAt (field : MeaningfulVoxelField Pos) (p : Pos) (k : Fin 8) : ℝ :=
  (field.voxel p).modeAmplitude k

section Finite
variable [Fintype Pos]

noncomputable def totalEnergy (field : MeaningfulVoxelField Pos) : ℝ :=
  ∑ p : Pos, (field.voxel p).totalEnergy

theorem totalEnergy_nonneg (field : MeaningfulVoxelField Pos) : 0 ≤ field.totalEnergy := by
  unfold totalEnergy
  apply Finset.sum_nonneg
  intro p _
  unfold MeaningfulVoxel.totalEnergy
  apply Finset.sum_nonneg
  intro k _
  apply sq_nonneg

def allNeutral (field : MeaningfulVoxelField Pos) : Prop :=
  ∀ p : Pos, isNeutral (field.voxel p)

def isNeutralField (field : MeaningfulVoxelField Pos) : Prop :=
  allNeutral field

end Finite

section Spectrum
variable [Fintype Pos]

noncomputable def fieldSpectrum (field : MeaningfulVoxelField Pos) : Fin 8 → ℂ :=
  fun k => ∑ p : Pos, (field.voxel p).frequencySpectrum k

noncomputable def fieldDC (field : MeaningfulVoxelField Pos) : ℂ :=
  field.fieldSpectrum 0

def spectrallyNeutral (field : MeaningfulVoxelField Pos) : Prop :=
  field.fieldDC = 0

theorem allNeutral_implies_spectrallyNeutral (field : MeaningfulVoxelField Pos) :
    field.allNeutral → field.spectrallyNeutral := by
  intro h
  unfold spectrallyNeutral fieldDC fieldSpectrum
  rw [Finset.sum_eq_zero]
  intro p _
  exact h p

noncomputable def modePower (field : MeaningfulVoxelField Pos) (k : Fin 8) : ℝ :=
  ∑ p : Pos, (field.voxel p).modeAmplitude k ^ 2

theorem modePower_nonneg (field : MeaningfulVoxelField Pos) (k : Fin 8) : 0 ≤ field.modePower k := by
  unfold modePower
  apply Finset.sum_nonneg; intro _ _; apply sq_nonneg

noncomputable def dominantMode (field : MeaningfulVoxelField Pos) : Fin 8 :=
  let p1 := field.modePower 1
  let p2 := field.modePower 2
  let p3 := field.modePower 3
  let p4 := field.modePower 4
  let maxP := max (max p1 p2) (max p3 p4)
  if p1 = maxP then 1
  else if p2 = maxP then 2
  else if p3 = maxP then 3
  else 4

end Spectrum

def stepField (field : MeaningfulVoxelField Pos) (entering : Pos → Photon) : MeaningfulVoxelField Pos :=
  ⟨fun p =>
    let v := field.voxel p
    let new_photon := entering p
    ⟨fun phase =>
      if h : phase = 0 then new_photon
      else v.photon ⟨phase.val - 1, by omega⟩⟩⟩

def exitingPhotons (field : MeaningfulVoxelField Pos) : Pos → Photon :=
  fun p => (field.voxel p).photon 7

theorem stepField_phase_zero (field : MeaningfulVoxelField Pos) (entering : Pos → Photon) (p : Pos) :
    (field.stepField entering).photonAt p 0 = entering p := by
  simp [stepField, photonAt]

theorem stepField_phase_succ (field : MeaningfulVoxelField Pos) (entering : Pos → Photon)
    (p : Pos) (k : Phase) (hk : k ≠ 0) :
    (field.stepField entering).photonAt p k = field.photonAt p ⟨k.val - 1, by omega⟩ := by
  simp [stepField, photonAt, hk]

def PhotonStream (Pos : Type) := ℕ → Pos → Photon

def iterateStep (field : MeaningfulVoxelField Pos) (stream : PhotonStream Pos) : ℕ → MeaningfulVoxelField Pos
  | 0 => field
  | n + 1 => (iterateStep field stream n).stepField (stream n)

def evolveOctave (field : MeaningfulVoxelField Pos) (stream : PhotonStream Pos) : MeaningfulVoxelField Pos :=
  iterateStep field stream 8

theorem evolveOctave_eq_iterate8 (field : MeaningfulVoxelField Pos) (stream : PhotonStream Pos) :
    field.evolveOctave stream = iterateStep field stream 8 := rfl

section EnergyConservation
variable [Fintype Pos]

noncomputable def enteringEnergy (entering : Pos → Photon) : ℝ :=
  ∑ p : Pos, (entering p).amplitude ^ 2

noncomputable def exitingEnergy (field : MeaningfulVoxelField Pos) : ℝ :=
  ∑ p : Pos, ((field.voxel p).photon 7).amplitude ^ 2

theorem Fin.sum_univ_eight {M : Type*} [AddCommMonoid M] (f : Fin 8 → M) :
    ∑ i : Fin 8, f i = f 0 + ∑ i : Fin 7, f i.succ := Fin.sum_univ_succ f

theorem Fin.sum_univ_eight_last {M : Type*} [AddCommMonoid M] (f : Fin 8 → M) :
    ∑ i : Fin 8, f i = (∑ i : Fin 7, f i.castSucc) + f 7 := Fin.sum_univ_castSucc f

theorem energy_balance (field : MeaningfulVoxelField Pos) (entering : Pos → Photon) :
    (field.stepField entering).totalEnergy =
    field.totalEnergy + enteringEnergy entering - field.exitingEnergy := by
  classical
  unfold MeaningfulVoxelField.totalEnergy enteringEnergy exitingEnergy
  have h_per : ∀ p : Pos,
      (MeaningfulVoxel.totalEnergy ((field.stepField entering).voxel p)) =
        MeaningfulVoxel.totalEnergy (field.voxel p)
          + (entering p).amplitude ^ 2
          - ((field.voxel p).photon 7).amplitude ^ 2 := by
    intro p
    have h_new_split :
        (∑ k : Fin 8, (((field.stepField entering).voxel p).photon k).amplitude ^ 2) =
          (((field.stepField entering).voxel p).photon 0).amplitude ^ 2
            + ∑ i : Fin 7, (((field.stepField entering).voxel p).photon i.succ).amplitude ^ 2 := by
      simpa using (Fin.sum_univ_eight (f := fun k : Fin 8 =>
        (((field.stepField entering).voxel p).photon k).amplitude ^ 2))
    have h_old_split :
        (∑ k : Fin 8, ((field.voxel p).photon k).amplitude ^ 2) =
          (∑ i : Fin 7, ((field.voxel p).photon i.castSucc).amplitude ^ 2)
            + ((field.voxel p).photon 7).amplitude ^ 2 := by
      simpa using (Fin.sum_univ_eight_last (f := fun k : Fin 8 =>
        ((field.voxel p).photon k).amplitude ^ 2))
    have h_shift : ∀ i : Fin 7,
        ((field.stepField entering).voxel p).photon i.succ = (field.voxel p).photon i.castSucc := by
      intro i
      have h := stepField_phase_succ (field := field) (entering := entering) (p := p) (k := (i.succ : Phase)) (by simp)
      have h_idx : (⟨(i.succ).val - 1, by omega⟩ : Phase) = i.castSucc := by ext; simp
      simpa [MeaningfulVoxelField.photonAt, h_idx] using h
    unfold MeaningfulVoxel.totalEnergy
    calc
      (∑ k : Phase, (((field.stepField entering).voxel p).photon k).amplitude ^ 2)
          = (((field.stepField entering).voxel p).photon 0).amplitude ^ 2
              + ∑ i : Fin 7, (((field.stepField entering).voxel p).photon i.succ).amplitude ^ 2 := by simpa using h_new_split
      _ = (entering p).amplitude ^ 2
              + ∑ i : Fin 7, ((field.voxel p).photon i.castSucc).amplitude ^ 2 := by
                have h0 : ((field.stepField entering).voxel p).photon 0 = entering p := by simp [stepField]
                simp [h0, h_shift]
      _ = (∑ k : Phase, ((field.voxel p).photon k).amplitude ^ 2)
              + (entering p).amplitude ^ 2
              - ((field.voxel p).photon 7).amplitude ^ 2 := by
                have h_partial :
                    (∑ i : Fin 7, ((field.voxel p).photon i.castSucc).amplitude ^ 2) =
                      (∑ k : Phase, ((field.voxel p).photon k).amplitude ^ 2) - ((field.voxel p).photon 7).amplitude ^ 2 := by
                  have := h_old_split; linarith
                linarith
  have : (∑ p : Pos, MeaningfulVoxel.totalEnergy ((field.stepField entering).voxel p))
        = (∑ p : Pos, MeaningfulVoxel.totalEnergy (field.voxel p))
          + (∑ p : Pos, (entering p).amplitude ^ 2)
          - (∑ p : Pos, ((field.voxel p).photon 7).amplitude ^ 2) := by
    calc
      (∑ p : Pos, MeaningfulVoxel.totalEnergy ((field.stepField entering).voxel p))
          = ∑ p : Pos,
              (MeaningfulVoxel.totalEnergy (field.voxel p)
                + (entering p).amplitude ^ 2
                - ((field.voxel p).photon 7).amplitude ^ 2) := by
                refine Finset.sum_congr rfl ?_; intro p _; exact h_per p
      _ = (∑ p : Pos, MeaningfulVoxel.totalEnergy (field.voxel p))
            + (∑ p : Pos, (entering p).amplitude ^ 2)
            - (∑ p : Pos, ((field.voxel p).photon 7).amplitude ^ 2) := by
            simp [sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib, add_assoc, add_left_comm, add_comm]
  simpa [MeaningfulVoxelField.totalEnergy, MeaningfulVoxel.totalEnergy] using this

end EnergyConservation

section NeutralityAccounting
variable [Fintype Pos]

noncomputable def voxelTimeSum (field : MeaningfulVoxelField Pos) (p : Pos) : ℂ :=
  ∑ k : Phase, (field.voxel p).toComplexSignal k

theorem voxelTimeSum_eq_zero_iff_neutral (field : MeaningfulVoxelField Pos) (p : Pos) :
    voxelTimeSum field p = 0 ↔ isNeutral (field.voxel p) := by
  simpa [voxelTimeSum] using (neutral_iff_zero_sum (v := field.voxel p)).symm

theorem voxelTimeSum_stepField (field : MeaningfulVoxelField Pos) (entering : Pos → Photon) (p : Pos) :
    voxelTimeSum (field.stepField entering) p =
      voxelTimeSum field p
        + (entering p).toComplex
        - (field.exitingPhotons p).toComplex := by
  classical
  unfold voxelTimeSum
  have h_new_split :
      (∑ k : Fin 8, ((field.stepField entering).voxel p).toComplexSignal k) =
        ((field.stepField entering).voxel p).toComplexSignal 0
          + ∑ i : Fin 7, ((field.stepField entering).voxel p).toComplexSignal i.succ := by
    simpa using (Fin.sum_univ_eight (f := fun k : Fin 8 =>
      ((field.stepField entering).voxel p).toComplexSignal k))
  have h_shift : ∀ i : Fin 7,
      ((field.stepField entering).voxel p).toComplexSignal i.succ =
        (field.voxel p).toComplexSignal i.castSucc := by
    intro i
    unfold MeaningfulVoxel.toComplexSignal
    have h := stepField_phase_succ (field := field) (entering := entering) (p := p) (k := (i.succ : Phase)) (by simp)
    have h_idx : (⟨(i.succ).val - 1, by omega⟩ : Phase) = i.castSucc := by ext; simp
    simpa [MeaningfulVoxelField.photonAt, MeaningfulVoxel.toComplexSignal, h_idx] using congrArg Photon.toComplex h
  have h0 : ((field.stepField entering).voxel p).toComplexSignal 0 = (entering p).toComplex := by
    unfold MeaningfulVoxel.toComplexSignal; simp [MeaningfulVoxelField.stepField]
  have h7 : (field.exitingPhotons p).toComplex = ((field.voxel p).toComplexSignal 7) := by
    unfold MeaningfulVoxelField.exitingPhotons MeaningfulVoxel.toComplexSignal; rfl
  have h_old_split :
      (∑ k : Fin 8, (field.voxel p).toComplexSignal k) =
        (∑ i : Fin 7, (field.voxel p).toComplexSignal i.castSucc) + (field.voxel p).toComplexSignal 7 := by
    simpa using (Fin.sum_univ_eight_last (f := fun k : Fin 8 =>
      (field.voxel p).toComplexSignal k))
  calc
    (∑ k : Phase, ((field.stepField entering).voxel p).toComplexSignal k)
        = ((field.stepField entering).voxel p).toComplexSignal 0
            + ∑ i : Fin 7, ((field.stepField entering).voxel p).toComplexSignal i.succ := by simpa using h_new_split
    _ = (entering p).toComplex + ∑ i : Fin 7, (field.voxel p).toComplexSignal i.castSucc := by simp [h0, h_shift]
    _ = (∑ k : Phase, (field.voxel p).toComplexSignal k) + (entering p).toComplex - (field.voxel p).toComplexSignal 7 := by
              have h_partial :
                  (∑ i : Fin 7, (field.voxel p).toComplexSignal i.castSucc) =
                    (∑ k : Phase, (field.voxel p).toComplexSignal k) - (field.voxel p).toComplexSignal 7 := by
                calc
                  (∑ i : Fin 7, (field.voxel p).toComplexSignal i.castSucc)
                      = ((∑ i : Fin 7, (field.voxel p).toComplexSignal i.castSucc) + (field.voxel p).toComplexSignal 7)
                          - (field.voxel p).toComplexSignal 7 := by simp [add_sub_cancel]
                  _ = (∑ k : Phase, (field.voxel p).toComplexSignal k) - (field.voxel p).toComplexSignal 7 := by simpa [h_old_split]
              simp [h_partial, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ = voxelTimeSum field p + (entering p).toComplex - (field.exitingPhotons p).toComplex := by
              simp [voxelTimeSum, h7, add_assoc, add_left_comm, add_comm]

end NeutralityAccounting

structure SpatialStencil (Pos : Type) where
  Dir : Type
  [DirFintype : Fintype Dir]
  src : Pos → Dir → Pos
  weight : Dir → ℂ

attribute [instance] SpatialStencil.DirFintype

namespace SpatialStencil
variable {Pos : Type}

noncomputable def enteringComplex (S : SpatialStencil Pos) (field : MeaningfulVoxelField Pos) (p : Pos) : ℂ :=
  ∑ d : S.Dir, S.weight d * (field.exitingPhotons (S.src p d)).toComplex

noncomputable def enteringPhoton (S : SpatialStencil Pos) (field : MeaningfulVoxelField Pos) (p : Pos) : Photon :=
  Photon.ofComplex (S.enteringComplex field p)

noncomputable def stepFieldCoupled (S : SpatialStencil Pos) (field : MeaningfulVoxelField Pos) :
    MeaningfulVoxelField Pos :=
  field.stepField (fun p => S.enteringPhoton field p)

section Energy
variable [Fintype Pos]

theorem energy_balance_stepFieldCoupled (S : SpatialStencil Pos) (field : MeaningfulVoxelField Pos) :
    (S.stepFieldCoupled field).totalEnergy =
      field.totalEnergy
        + enteringEnergy (fun p => S.enteringPhoton field p)
        - field.exitingEnergy := by
  simpa [SpatialStencil.stepFieldCoupled] using
    (energy_balance (field := field) (entering := fun p => S.enteringPhoton field p))

theorem voxelTimeSum_stepFieldCoupled (S : SpatialStencil Pos) (field : MeaningfulVoxelField Pos) (p : Pos) :
    voxelTimeSum (S.stepFieldCoupled field) p =
      voxelTimeSum field p
        + (S.enteringPhoton field p).toComplex
        - (field.exitingPhotons p).toComplex := by
  simpa [SpatialStencil.stepFieldCoupled] using
    (voxelTimeSum_stepField (field := field) (entering := fun q => S.enteringPhoton field q) (p := p))

end Energy
end SpatialStencil

structure VoxelLattice (Pos : Type) where
  faceSrc : Pos → Fin 6 → Pos
  edgeSrc : Pos → Fin 12 → Pos

namespace VoxelLattice
variable {Pos : Type}

noncomputable def facePlusEdgeStencil (L : VoxelLattice Pos) (wFace wEdge : ℂ) : SpatialStencil Pos :=
  { Dir := Sum (Fin 6) (Fin 12)
    src := fun p d =>
      match d with
      | Sum.inl d6 => L.faceSrc p d6
      | Sum.inr d12 => L.edgeSrc p d12
    weight := fun d =>
      match d with
      | Sum.inl _ => wFace
      | Sum.inr _ => wEdge }

end VoxelLattice

section ThetaDynamics
variable [Fintype Pos]

noncomputable def voxelFlux (v : MeaningfulVoxel) : ℝ :=
  ∑ k : Fin 8, v.modeAmplitude k

noncomputable def totalFlux (field : MeaningfulVoxelField Pos) : ℝ :=
  ∑ p : Pos, voxelFlux (field.voxel p)

noncomputable def fieldPhase (field : MeaningfulVoxelField Pos) : ℝ :=
  let total_amp := ∑ p : Pos, ∑ k : Phase, ((field.voxel p).photon k).amplitude
  if total_amp > 0 then
    (∑ p : Pos, ∑ k : Phase,
      ((field.voxel p).photon k).amplitude * ((field.voxel p).photon k).phase_offset) / total_amp
  else 0

/-- In RS-native units, τ₀ = 1 tick (positive by definition). -/
lemma tick_pos : 0 < tick := by simp [tick]

/-- Field phase evolution hypothesis (RS-native units).

    In RS-native units, phase advances by octave = 8 ticks per cycle.
    The flux-to-phase relationship simplifies in these units. -/
def H_FieldPhaseEvolution (field : MeaningfulVoxelField Pos) (stream : PhotonStream Pos) : Prop :=
  let evolved := field.evolveOctave stream
  -- In RS-native: 8 * tick = octave = 8
  fieldPhase evolved = fieldPhase field + field.totalFlux

end ThetaDynamics

section Coherence
variable [Fintype Pos]

noncomputable def spectralCoherence (field : MeaningfulVoxelField Pos) : ℝ :=
  if Fintype.card Pos ≤ 1 then 1
  else
    let mean_spectrum := fun k => (∑ p : Pos, (field.voxel p).modeAmplitude k) / Fintype.card Pos
    let variance := ∑ k : Fin 8, ∑ p : Pos, ((field.voxel p).modeAmplitude k - mean_spectrum k) ^ 2
    let total := ∑ k : Fin 8, ∑ p : Pos, (field.voxel p).modeAmplitude k ^ 2
    if total > 0 then 1 - variance / total else 1

theorem variance_nonneg' (field : MeaningfulVoxelField Pos) (mean_spectrum : Fin 8 → ℝ) :
    0 ≤ ∑ k : Fin 8, ∑ p : Pos, ((field.voxel p).modeAmplitude k - mean_spectrum k) ^ 2 := by
  apply Finset.sum_nonneg; intro k _; apply Finset.sum_nonneg; intro p _; exact sq_nonneg _

/-- **LEMMA**: Mean-centered variance is at most the second moment.

    This is the standard statistical inequality: Var(X) = E[X²] - E[X]² ≤ E[X²].

    Proof: Σ(x - μ)² = Σx² - 2μΣx + nμ² = Σx² - nμ² ≤ Σx² -/
theorem mean_variance_le_total {Pos : Type} [Fintype Pos] (x : Pos → ℝ) :
    let μ := (∑ p : Pos, x p) / Fintype.card Pos
    ∑ p : Pos, (x p - μ) ^ 2 ≤ ∑ p : Pos, x p ^ 2 := by
  classical
  intro μ
  have h_expand : ∀ p, (x p - μ) ^ 2 = x p ^ 2 - 2 * μ * x p + μ ^ 2 := fun p => by ring
  simp_rw [h_expand]

  have hdecomp : (∑ p : Pos, (x p ^ 2 - 2 * μ * x p + μ ^ 2)) =
      (∑ p : Pos, x p ^ 2) - (∑ p : Pos, 2 * μ * x p) + (Fintype.card Pos : ℝ) * μ ^ 2 := by
    have h1 : (∑ p : Pos, (x p ^ 2 - 2 * μ * x p + μ ^ 2)) =
        (∑ p : Pos, (x p ^ 2 - 2 * μ * x p)) + (∑ _p : Pos, μ ^ 2) := by
      simp [Finset.sum_add_distrib]
    rw [h1]
    simp [sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

  rw [hdecomp]

  have hsum_mul : (∑ p : Pos, 2 * μ * x p) = 2 * μ * (∑ p : Pos, x p) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (Finset.mul_sum (s := (Finset.univ : Finset Pos)) (f := x) (a := (2 * μ))).symm

  have h_sum_eq : 2 * μ * (∑ p : Pos, x p) = 2 * (Fintype.card Pos : ℝ) * μ ^ 2 := by
    simp only [μ]
    by_cases h_card : (Fintype.card Pos : ℝ) = 0
    · simp [h_card]
    · field_simp [h_card]

  have hsum_eq' : (∑ p : Pos, 2 * μ * x p) = 2 * (Fintype.card Pos : ℝ) * μ ^ 2 := by
    calc
      (∑ p : Pos, 2 * μ * x p) = 2 * μ * (∑ p : Pos, x p) := hsum_mul
      _ = 2 * (Fintype.card Pos : ℝ) * μ ^ 2 := h_sum_eq

  rw [hsum_eq']

  have hnonneg : 0 ≤ (Fintype.card Pos : ℝ) * μ ^ 2 := by
    have hcard : 0 ≤ (Fintype.card Pos : ℝ) := by exact_mod_cast Nat.cast_nonneg (Fintype.card Pos)
    exact mul_nonneg hcard (sq_nonneg μ)

  have hrew :
      (∑ p : Pos, x p ^ 2) - (2 * (Fintype.card Pos : ℝ) * μ ^ 2) + (Fintype.card Pos : ℝ) * μ ^ 2
        = (∑ p : Pos, x p ^ 2) - (Fintype.card Pos : ℝ) * μ ^ 2 := by
    ring

  simpa [hrew] using (sub_le_self (∑ p : Pos, x p ^ 2) hnonneg)

theorem spectralCoherence_bounded (field : MeaningfulVoxelField Pos) :
    0 ≤ field.spectralCoherence ∧ field.spectralCoherence ≤ 1 := by
  unfold spectralCoherence
  by_cases h_card : Fintype.card Pos ≤ 1
  · simp only [h_card, ↓reduceIte]; exact ⟨zero_le_one, le_refl 1⟩
  · simp only [h_card, ↓reduceIte]
    set mean_spectrum := fun k => (∑ p : Pos, (field.voxel p).modeAmplitude k) / Fintype.card Pos
    set variance := ∑ k : Fin 8, ∑ p : Pos, ((field.voxel p).modeAmplitude k - mean_spectrum k) ^ 2
    set total := ∑ k : Fin 8, ∑ p : Pos, (field.voxel p).modeAmplitude k ^ 2
    split_ifs with h_tot
    · have h_var_nn : 0 ≤ variance := variance_nonneg' field mean_spectrum
      have h_var_le : variance ≤ total := by
        apply Finset.sum_le_sum; intro k _; exact mean_variance_le_total _
      have h_ratio_le : variance / total ≤ 1 := by rw [div_le_one h_tot]; exact h_var_le
      have h_ratio_nn : 0 ≤ variance / total := div_nonneg h_var_nn (le_of_lt h_tot)
      constructor <;> linarith
    · exact ⟨zero_le_one, le_refl 1⟩

end Coherence
end MeaningfulVoxelField
end OctaveKernel
end IndisputableMonolith
