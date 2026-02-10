import IndisputableMonolith.ClassicalBridge.Fluids.Galerkin2D
import IndisputableMonolith.ClassicalBridge.Fluids.LNALSemantics

namespace IndisputableMonolith.ClassicalBridge.Fluids

/-!
# Simulation2D (Milestone M3)

This file states the *one-step simulation* bridge between:
- the discrete 2D Galerkin model (`Galerkin2D`), and
- a spatial LNAL execution semantics (`LNALSemantics.independent`) applied to an encoded field.

At this milestone we do **not** attempt to prove the analytic correctness of the simulation;
instead we package the required claim as an explicit `SimulationHypothesis` (no `axiom`, no `sorry`).
-/

open IndisputableMonolith.ClassicalBridge.Fluids

namespace Simulation2D

open IndisputableMonolith.LNAL
open IndisputableMonolith.ClassicalBridge.Fluids.LNALSemantics
open IndisputableMonolith.ClassicalBridge.Fluids.Encoding

/-!
## A concrete (nontrivial) 1-step simulation instance

The current spatial semantics is **independent per voxel**, so the only operations we can
fully simulate without additional hypotheses are those that act locally on the encoding.

Here we provide a simple, explicit example:
- LNAL program: constant `FOLD 1` (increments `nuPhi` by `+1`, with `clampI32`).
- Discrete step: update each Galerkin coefficient by replacing it with an **integer** whose
  sign matches `coeffSign` and whose magnitude is `clampI32 (coeffMag x + 1)`.

This is not yet a Navier–Stokes time step; it’s a proved, quantitative “register-step ↔ encoded-step”
example that we can build on once multi-voxel coupling is introduced.
-/

/-- A nontrivial LNAL program: increment `nuPhi` by `+1` at every instruction pointer. -/
@[simp] def foldPlusOneProgram : LProgram :=
  fun _ => LInstr.fold 1

/-- One-voxel semantics for `foldPlusOneProgram`: increment `nuPhi` by `+1` (clamped); leave `aux5` unchanged. -/
lemma voxelStep_foldPlusOneProgram (v : LNALVoxel) :
    voxelStep foldPlusOneProgram v = ({ v.1 with nuPhi := clampI32 (v.1.nuPhi + 1) }, v.2) := by
  rcases v with ⟨r6, a5⟩
  simp [LNALSemantics.voxelStep, foldPlusOneProgram, lStep, -clampI32]

/-- The corresponding discrete step on encoded Galerkin coefficients. -/
noncomputable def foldPlusOneStep {N : ℕ} (u : GalerkinState N) : GalerkinState N :=
  WithLp.toLp 2 (fun i : ((modes N) × Fin 2) =>
    let x : ℝ := u i
    let m : Int := clampI32 (coeffMag x + 1)
    let z : Int := (coeffSign x) * m
    (z : ℝ))

lemma floor_abs_intCast (z : Int) : Int.floor (|((z : ℝ))|) = |z| := by
  have habs : |((z : ℝ))| = ((|z| : Int) : ℝ) := by
    simp
  rw [habs]
  simpa using (Int.floor_intCast (R := ℝ) (z := |z|))

lemma cast_lt_zero_iff {z : Int} : ((z : ℝ) < 0) ↔ z < 0 := by
  constructor
  · intro hz
    by_contra h
    have : (0 : Int) ≤ z := le_of_not_gt h
    have : (0 : ℝ) ≤ (z : ℝ) := by exact_mod_cast this
    exact (not_lt_of_ge this) hz
  · intro hz
    exact_mod_cast hz

lemma clampI32_pos_of_ge_one {x : Int} (hx : 1 ≤ x) : 0 < clampI32 x := by
  -- From `x ≥ 1`, the negative-saturation branch is impossible; then either we saturate high,
  -- or we return `x` itself. In both cases the result is positive.
  have hx0 : (0 : Int) ≤ x := le_trans (by decide : (0 : Int) ≤ 1) hx
  have hnot : ¬ x ≤ (-i32Bound) := by
    have hi : (-i32Bound : Int) < 0 := by
      have : (0 : Int) < i32Bound := by decide
      linarith
    exact not_le_of_gt (lt_of_lt_of_le hi hx0)
  -- Convert `hnot` to the numeral form used by definitional unfolding of `i32Bound`.
  have hnot' : ¬ x ≤ (-2147483648 : Int) := by simpa using hnot
  dsimp [clampI32]
  rw [if_neg hnot']
  by_cases h₂ : (2147483648 : Int) ≤ x
  · rw [if_pos h₂]
    have : (1 : Int) < (2147483648 : Int) := by decide
    linarith
  · rw [if_neg h₂]
    exact lt_of_lt_of_le (by decide : (0 : Int) < 1) hx

lemma coeffMag_foldPlusOneStep {N : ℕ} (u : GalerkinState N) (i : (modes N) × Fin 2) :
    coeffMag ((foldPlusOneStep u) i) = clampI32 (coeffMag (u i) + 1) := by
  classical
  set x : ℝ := u i
  have hx1 : (1 : Int) ≤ coeffMag x + 1 := by
    have hx0 : (0 : Int) ≤ coeffMag x := (Int.floor_nonneg (a := |x|)).2 (abs_nonneg x)
    linarith
  -- Let `m` be the (positive) clamped magnitude and `z` the signed integer we encode as a real.
  set m : Int := clampI32 (coeffMag x + 1)
  set z : Int := coeffSign x * m
  have hmpos : 0 < m := by
    simpa [m] using (clampI32_pos_of_ge_one (x := coeffMag x + 1) hx1)
  have hm0 : 0 ≤ m := le_of_lt hmpos
  -- Expand `coeffMag` and reduce to a floor/abs fact on an integer cast.
  -- `foldPlusOneStep u i` is literally `(z : ℝ)`.
  have hcore :
      coeffMag ((foldPlusOneStep u) i) = Int.floor (|((z : ℝ))|) := by
    simp [coeffMag, foldPlusOneStep, x, m, z, -clampI32]
  -- Now compute the floor of the abs cast and simplify `|z|`.
  calc
    coeffMag ((foldPlusOneStep u) i)
        = Int.floor (|((z : ℝ))|) := hcore
    _ = |z| := floor_abs_intCast z
    _ = m := by
      by_cases hx : x < 0
      · have hz : z = -m := by simp [z, coeffSign, hx]
        rw [hz]
        -- `| -m | = |m| = m` since `m ≥ 0`.
        simp [abs_of_nonneg hm0]
      · have hz : z = m := by simp [z, coeffSign, hx]
        rw [hz]
        simp [abs_of_nonneg hm0]

lemma coeffSign_foldPlusOneStep {N : ℕ} (u : GalerkinState N) (i : (modes N) × Fin 2) :
    coeffSign ((foldPlusOneStep u) i) = coeffSign (u i) := by
  classical
  set x : ℝ := u i
  have hx1 : (1 : Int) ≤ coeffMag x + 1 := by
    have hx0 : (0 : Int) ≤ coeffMag x := (Int.floor_nonneg (a := |x|)).2 (abs_nonneg x)
    linarith
  have hmpos : 0 < clampI32 (coeffMag x + 1) :=
    clampI32_pos_of_ge_one (x := coeffMag x + 1) hx1
  by_cases hx : x < 0
  ·
    -- `x < 0` ⇒ `coeffSign x = -1`, and the step coefficient is negative (since the magnitude is positive).
    have hzInt : (coeffSign x) * clampI32 (coeffMag x + 1) < 0 := by
      have hneg : -(clampI32 (coeffMag x + 1)) < 0 := neg_neg_of_pos hmpos
      calc
        (coeffSign x) * clampI32 (coeffMag x + 1)
            = (-1) * clampI32 (coeffMag x + 1) := by simp [coeffSign, hx]
        _ = -(clampI32 (coeffMag x + 1)) := by ring
        _ < 0 := hneg
    have hzReal :
        (((coeffSign x) * clampI32 (coeffMag x + 1) : Int) : ℝ) < 0 :=
      (cast_lt_zero_iff (z := (coeffSign x) * clampI32 (coeffMag x + 1))).2 hzInt
    have hy : (foldPlusOneStep u) i < 0 := by
      simpa [foldPlusOneStep, x] using hzReal
    simp [coeffSign, hx, hy, x]
  ·
    -- `¬ x < 0` ⇒ `coeffSign x = 1`, and the step coefficient is nonnegative.
    have hzInt : (0 : Int) ≤ (coeffSign x) * clampI32 (coeffMag x + 1) := by
      have hm0 : (0 : Int) ≤ clampI32 (coeffMag x + 1) := le_of_lt hmpos
      simpa [coeffSign, hx] using hm0
    have hzReal :
        (0 : ℝ) ≤ (((coeffSign x) * clampI32 (coeffMag x + 1) : Int) : ℝ) := by
      exact_mod_cast hzInt
    have hy : ¬ (foldPlusOneStep u) i < 0 := by
      have hy0 : (0 : ℝ) ≤ (foldPlusOneStep u) i := by
        simpa [foldPlusOneStep, x] using hzReal
      exact not_lt_of_ge hy0
    simp [coeffSign, hx, hy, x]

lemma decide_lt_zero_foldPlusOneStep {N : ℕ} (u : GalerkinState N) (i : (modes N) × Fin 2) :
    decide ((foldPlusOneStep u) i < 0) = decide (u i < 0) := by
  classical
  set x : ℝ := u i
  have hx1 : (1 : Int) ≤ coeffMag x + 1 := by
    have hx0 : (0 : Int) ≤ coeffMag x := (Int.floor_nonneg (a := |x|)).2 (abs_nonneg x)
    linarith
  have hmpos : 0 < clampI32 (coeffMag x + 1) :=
    clampI32_pos_of_ge_one (x := coeffMag x + 1) hx1
  by_cases hx : x < 0
  ·
    have hzInt : (coeffSign x) * clampI32 (coeffMag x + 1) < 0 := by
      have hneg : -(clampI32 (coeffMag x + 1)) < 0 := neg_neg_of_pos hmpos
      calc
        (coeffSign x) * clampI32 (coeffMag x + 1)
            = (-1) * clampI32 (coeffMag x + 1) := by simp [coeffSign, hx]
        _ = -(clampI32 (coeffMag x + 1)) := by ring
        _ < 0 := hneg
    have hzReal :
        (((coeffSign x) * clampI32 (coeffMag x + 1) : Int) : ℝ) < 0 :=
      (cast_lt_zero_iff (z := (coeffSign x) * clampI32 (coeffMag x + 1))).2 hzInt
    have hy : (foldPlusOneStep u) i < 0 := by
      simpa [foldPlusOneStep, x] using hzReal
    simp [x, hx, hy]
  ·
    have hzInt : (0 : Int) ≤ (coeffSign x) * clampI32 (coeffMag x + 1) := by
      have hm0 : (0 : Int) ≤ clampI32 (coeffMag x + 1) := le_of_lt hmpos
      simpa [coeffSign, hx] using hm0
    have hzReal :
        (0 : ℝ) ≤ (((coeffSign x) * clampI32 (coeffMag x + 1) : Int) : ℝ) := by
      exact_mod_cast hzInt
    have hy : ¬ (foldPlusOneStep u) i < 0 := by
      have hy0 : (0 : ℝ) ≤ (foldPlusOneStep u) i := by
        simpa [foldPlusOneStep, x] using hzReal
      exact not_lt_of_ge hy0
    simp [x, hx, hy]

lemma voxelStep_foldPlusOne_encodeIndex {N : ℕ} (u : GalerkinState N) (i : (modes N) × Fin 2) :
    voxelStep foldPlusOneProgram (encodeIndex u i) = encodeIndex (foldPlusOneStep u) i := by
  classical
  -- use the closed-form voxel semantics for `FOLD 1`, then rewrite encoding fields
  simp [voxelStep_foldPlusOneProgram, encodeIndex, coeffMag_foldPlusOneStep, coeffSign_foldPlusOneStep,
    decide_lt_zero_foldPlusOneStep, -clampI32]

/-!
## Decoding the encoding (for weaker, decode-based simulation)

Exact commutation at the *encoding* level is too strict for decay steps that can hit `0` and flip
sign bits (`sigma/phiE`) when re-encoded. A practical workaround is to compare **decoded**
coefficients after stepping.
-/

/-- Decode a nonnegative magnitude from a register `nuPhi`.

We interpret negative values as `0` (via `Int.toNat`) so that a decrement step can “saturate at 0”
even if the underlying register becomes negative. -/
def decodeMag (z : Int) : Int :=
  Int.ofNat (Int.toNat z)

/-- Decode a single real coefficient from a voxel: sign from `sigma`, magnitude from `nuPhi`. -/
noncomputable def decodeCoeff (v : LNALVoxel) : ℝ :=
  ((v.1.sigma * decodeMag v.1.nuPhi : Int) : ℝ)

/-- Decode an `LNALField` (of the expected Galerkin encoding length) back to a Galerkin state.

This is a left-inverse of `encodeGalerkin2D` only up to the coarse quantization used by `coeffMag`.
-/
noncomputable def decodeGalerkin2D {N : ℕ} (field : LNALField)
    (hsize : field.size = Fintype.card ((modes N) × Fin 2)) : GalerkinState N :=
  WithLp.toLp 2 (fun i : ((modes N) × Fin 2) =>
    let j : Fin (Fintype.card ((modes N) × Fin 2)) := (Fintype.equivFin ((modes N) × Fin 2)) i
    decodeCoeff (field[(Fin.cast hsize.symm j)]))

/-- Hypothesis: one LNAL spatial step simulates one discrete Galerkin step (exactly). -/
structure SimulationHypothesis (N : ℕ) where
  /-- The LNAL program used for the simulation. -/
  P : LProgram
  /-- The discrete (time-stepping) map on Galerkin states. -/
  step : GalerkinState N → GalerkinState N
  /-- One-step commutation: execute then encode = encode then step. -/
  comm :
      ∀ u : GalerkinState N,
        (independent.step P (encodeGalerkin2D u)) = encodeGalerkin2D (step u)

/-- Trivial simulation: use the `LISTEN noop` LNAL program and take the discrete step as `id`. -/
@[simp] def SimulationHypothesis.trivial (N : ℕ) : SimulationHypothesis N :=
  { P := listenNoopProgram
    step := id
    comm := by
      intro u
      simp }

/-- A concrete, nontrivial simulation instance: `FOLD 1` corresponds to `foldPlusOneStep`. -/
noncomputable def SimulationHypothesis.foldPlusOne (N : ℕ) : SimulationHypothesis N :=
  { P := foldPlusOneProgram
    step := foldPlusOneStep
    comm := by
      intro u
      classical
      -- Prove array equality by pointwise equality.
      refine Array.ext (by simp [LNALSemantics.independent, encodeGalerkin2D]) ?_
      intro j hj₁ hj₂
      have hj : j < Fintype.card ((modes N) × Fin 2) := by
        simpa [encodeGalerkin2D] using hj₂
      let jFin : Fin (Fintype.card ((modes N) × Fin 2)) := ⟨j, hj⟩
      -- Reduce to the single-voxel commutation lemma.
      simpa [LNALSemantics.independent, encodeGalerkin2D, foldPlusOneProgram] using
        (show voxelStep foldPlusOneProgram (encodeIndex u ((Fintype.equivFin ((modes N) × Fin 2)).symm jFin))
            = encodeIndex (foldPlusOneStep u) ((Fintype.equivFin ((modes N) × Fin 2)).symm jFin) from by
            simpa using
              (voxelStep_foldPlusOne_encodeIndex (u := u)
                (i := (Fintype.equivFin ((modes N) × Fin 2)).symm jFin))) }

/-- The one-step simulation lemma (directly from `SimulationHypothesis.comm`). -/
theorem simulation_one_step {N : ℕ} (H : SimulationHypothesis N) (u : GalerkinState N) :
    independent.step H.P (encodeGalerkin2D u) = encodeGalerkin2D (H.step u) :=
  H.comm u

/-!
## Decode-based simulation (weaker notion) and a diagonal decay step

For some local operations (e.g. sign-preserving decay of a magnitude register), exact commutation
`encode(step u) = step(encode u)` can fail due to sign-bit conventions at `0`.

We therefore also provide a **decode-based** simulation notion:
we compare decoded coefficients after executing the LNAL step.
-/

/-- Hypothesis: one LNAL spatial step simulates one discrete Galerkin step **after decoding**. -/
structure DecodedSimulationHypothesis (N : ℕ) where
  /-- The LNAL program used for the simulation. -/
  P : LProgram
  /-- The discrete (time-stepping) map on Galerkin states (on decoded/quantized coefficients). -/
  step : GalerkinState N → GalerkinState N
  /-- One-step commutation after decoding. -/
  comm :
      ∀ u : GalerkinState N,
        decodeGalerkin2D (N := N)
          (field := independent.step P (encodeGalerkin2D u))
          (hsize := by simp [LNALSemantics.independent, encodeGalerkin2D])
          = step u

/-- The one-step decoded simulation lemma (directly from `DecodedSimulationHypothesis.comm`). -/
theorem decoded_simulation_one_step {N : ℕ} (H : DecodedSimulationHypothesis N) (u : GalerkinState N) :
    decodeGalerkin2D (N := N)
      (field := independent.step H.P (encodeGalerkin2D u))
      (hsize := by simp [LNALSemantics.independent, encodeGalerkin2D])
      = H.step u :=
  H.comm u

/-- A constant LNAL program: decrement `nuPhi` by `1` (via `FOLD (-1)`). -/
@[simp] def foldMinusOneProgram : LProgram :=
  fun _ => LInstr.fold (-1)

/-- One-voxel semantics for `foldMinusOneProgram`: decrement `nuPhi` by `1` (clamped); leave `aux5` unchanged. -/
lemma voxelStep_foldMinusOneProgram (v : LNALVoxel) :
    voxelStep foldMinusOneProgram v = ({ v.1 with nuPhi := clampI32 (v.1.nuPhi + (-1)) }, v.2) := by
  rcases v with ⟨r6, a5⟩
  simp [LNALSemantics.voxelStep, foldMinusOneProgram, lStep, -clampI32]

/-- The corresponding discrete step on **decoded** Galerkin coefficients.

We mimic the VM update on `nuPhi` (via `clampI32`) and then decode a nonnegative magnitude using `decodeMag`. -/
noncomputable def foldMinusOneDecodedStep {N : ℕ} (u : GalerkinState N) : GalerkinState N :=
  WithLp.toLp 2 (fun i : ((modes N) × Fin 2) =>
    let x : ℝ := u i
    let m : Int := decodeMag (clampI32 (coeffMag x + (-1)))
    let z : Int := (coeffSign x) * m
    (z : ℝ))

/-- Decoding after a single `FOLD (-1)` step matches the corresponding decoded discrete step. -/
lemma decodeCoeff_voxelStep_foldMinusOne_encodeIndex {N : ℕ} (u : GalerkinState N) (i : (modes N) × Fin 2) :
    decodeCoeff (voxelStep foldMinusOneProgram (encodeIndex u i)) = (foldMinusOneDecodedStep u) i := by
  classical
  -- both sides reduce to the same signed-integer expression
  simp [decodeCoeff, foldMinusOneDecodedStep, decodeMag, voxelStep_foldMinusOneProgram, encodeIndex, -clampI32]

/-- A concrete, proved decay-step simulation instance (after decoding). -/
noncomputable def DecodedSimulationHypothesis.foldMinusOne (N : ℕ) : DecodedSimulationHypothesis N :=
  { P := foldMinusOneProgram
    step := foldMinusOneDecodedStep
    comm := by
      intro u
      classical
      -- Prove equality of Galerkin states by pointwise equality of coefficients.
      ext i
      -- Reduce to the single-voxel lemma `decodeCoeff_voxelStep_foldMinusOne_encodeIndex`.
      simp [decodeGalerkin2D, LNALSemantics.independent, encodeGalerkin2D,
        decodeCoeff_voxelStep_foldMinusOne_encodeIndex] }

end Simulation2D

end IndisputableMonolith.ClassicalBridge.Fluids
