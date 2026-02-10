import Mathlib
import IndisputableMonolith.Compat.FunctionIterate
import IndisputableMonolith.LNAL.Registers
import IndisputableMonolith.LNAL.Opcodes
import IndisputableMonolith.LNAL.VM

/-!
Compatibility note:

Some parts of this repo use `Int.abs` (an `Int → Int` absolute value).
Lean core exposes `Int.natAbs : Int → Nat`, but not `Int.abs` as an `Int`.

We define `Int.abs` here as a thin wrapper around `natAbs` so downstream
LNAL invariants/certificates typecheck.
-/

namespace Int

/-- Absolute value as an `Int` (wrapper around `natAbs`). -/
def abs (z : Int) : Int := Int.ofNat z.natAbs

@[simp] lemma abs_zero : Int.abs 0 = 0 := by
  simp [Int.abs]

@[simp] lemma abs_one : Int.abs 1 = 1 := by
  simp [Int.abs]

@[simp] lemma abs_neg_one : Int.abs (-1) = 1 := by
  simp [Int.abs]

end Int

namespace IndisputableMonolith
namespace LNAL

/-- FLIP toggles exactly at mid-breath (511 for breathPeriod=1024), otherwise leaves `flipped` unchanged.

Note: this lemma assumes the VM is running (`s.halted = false`). When halted,
the VM does not execute opcodes (so FLIP does not toggle). -/
lemma lStep_flip_behavior (P : LProgram) (s : LState) (hRun : s.halted = false)
  (hop : (lFetch P s.ip).op = Opcode.FLIP) :
  let mid := breathPeriod / 2 - 1;
  ((s.breath = mid → (lStep P s).flipped = not s.flipped) ∧
   (s.breath ≠ mid → (lStep P s).flipped = s.flipped)) := by
  intro mid
  -- Rewrite the opcode hypothesis into the direct `P s.ip` form used by `lStep`.
  have hop' : (P s.ip).op = Opcode.FLIP := by
    simpa [lFetch] using hop
  -- In the running/FLIP branch, `lStep` sets `flipped` to `not` exactly at `mid`.
  simp [lStep, hRun, hop', mid]

/-- Scheduling rule: whenever winIdx8=7, the next opcode is BALANCE (and NOT in cycle mode,
    which has different reset semantics). -/
def balanceWhenIdx7 (P : LProgram) (s : LState) : Prop :=
  ∀ t, (Function.iterate (lStep P) t s).winIdx8 = 7 →
       (lFetch P (Function.iterate (lStep P) t s).ip).op = Opcode.BALANCE ∧
       (lFetch P (Function.iterate (lStep P) t s).ip).arg ≠ OpcodeArg.balance BalanceMode.cycle

/-- If the scheduler satisfies `balanceWhenIdx7`, every encountered boundary resets on the next step.

Note: `balanceWhenIdx7` excludes `BalanceMode.cycle` because that mode only resets at end-of-breath,
not at every window boundary. With `BalanceMode.window` (or other args), `winSum8` resets whenever
`winIdx8 = 7`.

Requires that the iterated state is running (`halted = false`); if halted, `lStep` is a no-op and
the window index would remain at 7. -/
lemma neutral_at_any_boundary (P : LProgram) (s : LState)
  (hBal : balanceWhenIdx7 P s) (t : Nat)
  (hIdx7 : (Function.iterate (lStep P) t s).winIdx8 = 7)
  (hRun : (Function.iterate (lStep P) t s).halted = false) :
  let sT := Function.iterate (lStep P) t s;
  (lStep P sT).winSum8 = 0 ∧ (lStep P sT).winIdx8 = 0 := by
  intro sT

  have hBalT := hBal t hIdx7
  have hOpBal : (lFetch P sT.ip).op = Opcode.BALANCE := hBalT.1
  have hNotCycle : (lFetch P sT.ip).arg ≠ OpcodeArg.balance BalanceMode.cycle := hBalT.2

  have hop' : (P sT.ip).op = Opcode.BALANCE := by simpa [lFetch] using hOpBal
  have hIdx7T : sT.winIdx8 = 7 := by simpa [sT] using hIdx7
  have hRunT : sT.halted = false := by simpa [sT] using hRun

  unfold lStep
  simp only [hRunT, ↓reduceIte]
  -- Running: execute BALANCE
  -- Split on the arg to handle all cases
  cases harg : (P sT.ip).arg with
  | balance mode =>
      cases mode with
      | cycle =>
          -- Contradiction with hNotCycle
          exfalso
          apply hNotCycle
          simpa [lFetch, harg]
      | window =>
          -- Window mode: winSum8 resets when winIdx8 = 7
          simp [hop', harg, hIdx7T]
  | none =>
      -- Fallback branch: winSum8 resets when winIdx8 = 7
      simp [hop', harg, hIdx7T]
  | fold dir =>
      simp [hop', harg, hIdx7T]
  | token act =>
      simp [hop', harg, hIdx7T]
  | listen mode =>
      simp [hop', harg, hIdx7T]

/-- Alignment predicate: breath ends only at window boundary (idx=7). -/
def alignedBoundaries (P : LProgram) (s : LState) : Prop :=
  ∀ t, (Function.iterate (lStep P) t s).breath = breathPeriod - 1 →
       (Function.iterate (lStep P) t s).winIdx8 = 7

/-- Alignment is preserved when shifting the starting state by iteration. -/
lemma alignedBoundaries_shift (P : LProgram) (s : LState)
  (hA : alignedBoundaries P s) (n : Nat) :
  alignedBoundaries P (Function.iterate (lStep P) n s) := by
  intro t hEnd
  -- Use iterate_add_apply: f^[m + n] x = f^[m] (f^[n] x)
  -- We need: f^[t] (f^[n] s) = f^[t + n] s, which is the symmetric form
  have hEq : Function.iterate (lStep P) t (Function.iterate (lStep P) n s) =
             Function.iterate (lStep P) (t + n) s :=
    (Function.iterate_add_apply (lStep P) t n s).symm
  -- Transfer the end-of-breath condition
  have hEnd' : (Function.iterate (lStep P) (t + n) s).breath = breathPeriod - 1 := by
    rwa [← hEq]
  -- Apply the original alignment predicate
  have hIdx : (Function.iterate (lStep P) (t + n) s).winIdx8 = 7 := hA (t + n) hEnd'
  -- Transfer back
  rwa [← hEq] at hIdx

/-- With aligned boundaries, `winIdx8` advances by +1 mod 8 each step.

Requires `halted = false` because `lStep` is a no-op when halted.
The alignment predicate ensures that even `BALANCE` with `BalanceMode.cycle` at end-of-breath
(which forces `winIdx8 := 0`) is consistent with the formula, since end-of-breath only occurs
at `winIdx8 = 7`, and `(7 + 1) % 8 = 0`. -/
lemma winIdx8_adv_aligned (P : LProgram) (s : LState)
  (hRun : s.halted = false)
  (hA : alignedBoundaries P s) :
  (lStep P s).winIdx8 = (s.winIdx8 + 1) % 8 := by
  cases hop : (P s.ip).op with
  | BALANCE =>
      cases harg : (P s.ip).arg with
      | balance mode =>
          cases mode with
          | cycle =>
              -- At end-of-breath, BALANCE cycle sets winIdx8 := 0
              -- At non-end-of-breath, it sets winIdx8 := advIdx
              by_cases hEnd : s.breath = 1023
              · -- End of breath (1023 = breathPeriod - 1): winIdx8 = 0
                -- By alignment, end-of-breath implies winIdx8 = 7
                have h7 : s.winIdx8 = 7 := hA 0 (by simpa [breathPeriod] using hEnd)
                simp [lStep, hRun, hop, harg, hEnd, h7]
              · -- Not end of breath: winIdx8 := advIdx = (s.winIdx8 + 1) % 8
                simp [lStep, hRun, hop, harg, hEnd]
          | window =>
              simp [lStep, hRun, hop, harg]
      | none =>
          simp [lStep, hRun, hop, harg]
      | fold dir =>
          simp [lStep, hRun, hop, harg]
      | token act =>
          simp [lStep, hRun, hop, harg]
      | listen mode =>
          simp [lStep, hRun, hop, harg]
  | _ =>
      simp [lStep, hRun, hop]

/-- For aligned boundaries, explicit formula for index after n steps.

Requires that all iterated states remain running (`halted = false`), since `winIdx8_adv_aligned`
requires a running state, and that `s.winIdx8 < 8` (normally guaranteed by the VM invariant). -/
lemma winIdx8_after_n_aligned (P : LProgram) (s : LState)
  (hIdx : s.winIdx8 < 8)
  (hA : alignedBoundaries P s)
  (hRunAll : ∀ k, (Function.iterate (lStep P) k s).halted = false) :
  ∀ n, (Function.iterate (lStep P) n s).winIdx8 = (s.winIdx8 + n) % 8 := by
  intro n
  induction n with
  | zero =>
      simp only [Function.iterate_zero, id_eq, Nat.add_zero]
      exact (Nat.mod_eq_of_lt hIdx).symm
  | succ n ih =>
      -- f^[n+1] s = f (f^[n] s) by iterate_succ_apply'
      have hStep : Function.iterate (lStep P) (n + 1) s = lStep P (Function.iterate (lStep P) n s) :=
        Function.iterate_succ_apply' (lStep P) n s
      rw [hStep]
      -- Apply winIdx8_adv_aligned to the n-th iterate
      have hRun_n : (Function.iterate (lStep P) n s).halted = false := hRunAll n
      have hA_n : alignedBoundaries P (Function.iterate (lStep P) n s) := alignedBoundaries_shift P s hA n
      have hAdv := winIdx8_adv_aligned P (Function.iterate (lStep P) n s) hRun_n hA_n
      rw [hAdv, ih]
      -- Goal: ((s.winIdx8 + n) % 8 + 1) % 8 = (s.winIdx8 + (n + 1)) % 8
      -- This is: (a % 8 + 1) % 8 = (a + 1) % 8 where a = s.winIdx8 + n
      conv_rhs => rw [← Nat.add_assoc]
      rw [Nat.add_mod, Nat.mod_mod_of_dvd, ← Nat.add_mod]
      decide

/-- If starting aligned at idx=0 with winSum8=0, and the scheduler balances at idx=7,
    then the window is neutral at every 8-step boundary across long runs.

    Requires:
    - `s.winIdx8 < 8` for the modular arithmetic
    - `s.winSum8 = 0` for the base case
    - `hRunAll` for all iterated states to be running (so BALANCE executes) -/
lemma neutral_every_8th_from0 (P : LProgram) (s : LState)
  (hIdx : s.winIdx8 < 8)
  (hA : alignedBoundaries P s) (hBal : balanceWhenIdx7 P s)
  (h0 : s.winIdx8 = 0) (hSum0 : s.winSum8 = 0)
  (hRunAll : ∀ k, (Function.iterate (lStep P) k s).halted = false) :
  ∀ k, (Function.iterate (lStep P) (8 * k) s).winIdx8 = 0 ∧ (Function.iterate (lStep P) (8 * k) s).winSum8 = 0 := by
  intro k
  induction k with
  | zero =>
      simp only [Nat.mul_zero, Function.iterate_zero, id_eq]
      exact ⟨h0, hSum0⟩
  | succ k ih =>
      -- At step 8*k + 7, winIdx8 = 7, so BALANCE runs and resets
      -- Step 8*(k+1) = 8*k + 8 is one step after 8*k + 7
      have hIdx7 : (Function.iterate (lStep P) (8 * k + 7) s).winIdx8 = 7 := by
        have := winIdx8_after_n_aligned P s hIdx hA hRunAll (8 * k + 7)
        simp only [h0, Nat.zero_add] at this
        -- (8*k + 7) % 8 = 7
        have h7 : (8 * k + 7) % 8 = 7 := by
          rw [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_eq_of_lt (by decide : 7 < 8)]
        rw [this, h7]
      -- Use neutral_at_any_boundary to show the reset
      have hRun7 : (Function.iterate (lStep P) (8 * k + 7) s).halted = false := hRunAll (8 * k + 7)
      have hReset := neutral_at_any_boundary P s hBal (8 * k + 7) hIdx7 hRun7
      -- The next step is 8*k + 8 = 8*(k+1)
      -- Goal: (f^[8*(k+1)] s).winIdx8 = 0 ∧ (f^[8*(k+1)] s).winSum8 = 0
      -- hReset: (lStep P (f^[8*k+7] s)).winSum8 = 0 ∧ (lStep P (f^[8*k+7] s)).winIdx8 = 0
      -- We need to show f^[8*(k+1)] s = lStep P (f^[8*k+7] s)
      have hStep : Function.iterate (lStep P) (8 * (k + 1)) s =
                   lStep P (Function.iterate (lStep P) (8 * k + 7) s) := by
        -- 8*(k+1) = 8k + 8 = (8k + 7) + 1
        conv_lhs => rw [show 8 * (k + 1) = (8 * k + 7) + 1 by omega]
        exact Function.iterate_succ_apply' (lStep P) (8 * k + 7) s
      rw [hStep]
      exact ⟨hReset.2, hReset.1⟩

/-- Token parity invariant: tokenCt ∈ {0,1}. -/
def TokenParityInvariant (s : LState) : Prop := (0 ≤ s.aux5.tokenCt) ∧ (s.aux5.tokenCt ≤ 1)

/-- Minimal SU(3) triad legality: limit transverse mode to −1,0,1. -/
def SU3Invariant (s : LState) : Prop := s.reg6.kPerp = (-1) ∨ s.reg6.kPerp = 0 ∨ s.reg6.kPerp = 1

/-- clamp01 yields a value in {0,1}. -/
lemma clamp01_bounds (x : Int) : 0 ≤ clamp01 x ∧ clamp01 x ≤ 1 := by
  unfold clamp01
  by_cases h0 : x ≤ 0
  · -- clamp01 x = 0
    simp [h0]
  · -- clamp01 x = 1 or x depending on whether 1 ≤ x
    by_cases h1 : 1 ≤ x
    · -- clamp01 x = 1
      simp [h0, h1]
    · -- clamp01 x = x, and we use only the guards to bound x.
      have hx0 : 0 ≤ x := le_of_lt (lt_of_not_ge h0)
      have hx1 : x ≤ 1 := le_of_lt (lt_of_not_ge h1)
      -- Reduce the definition, then discharge the resulting inequalities.
      simp [h0, h1, hx0, hx1]

/-- applyTokenAction always produces tokenCt in {0,1} via clamp01. -/
lemma applyTokenAction_tokenCt_bounds (a5 : Aux5) (act : TokenAction) :
    let result := applyTokenAction a5 act
    0 ≤ result.1.tokenCt ∧ result.1.tokenCt ≤ 1 := by
  cases act with
  | delta d => exact clamp01_bounds _
  | set v c => exact clamp01_bounds _

/-- lStep preserves tokenCt: either unchanged or goes through clamp01. -/
lemma lStep_tokenCt_bounds (P : LProgram) (s : LState)
    (h : 0 ≤ s.aux5.tokenCt ∧ s.aux5.tokenCt ≤ 1) :
    0 ≤ (lStep P s).aux5.tokenCt ∧ (lStep P s).aux5.tokenCt ≤ 1 := by
  by_cases hH : s.halted
  · simp [lStep, hH, h.1, h.2]
  · simp only [lStep, hH, ↓reduceIte]
    cases hop : (lFetch P s.ip).op with
    | LOCK => simp [hop, h.1, h.2]
    | FLIP => simp [hop, h.1, h.2]
    | BALANCE =>
        cases harg : (lFetch P s.ip).arg <;> simp [hop, harg, h.1, h.2]
    | FOLD => simp [hop, h.1, h.2]
    | LISTEN =>
        cases harg : (lFetch P s.ip).arg <;> simp [hop, harg, h.1, h.2]
    | SEED =>
        cases harg : (lFetch P s.ip).arg with
        | token act => simp only [hop, harg]; exact applyTokenAction_tokenCt_bounds _ _
        | _ => simp only [hop, harg]; exact applyTokenAction_tokenCt_bounds _ _
    | BRAID =>
        cases harg : (lFetch P s.ip).arg with
        | token act => simp only [hop, harg]; exact applyTokenAction_tokenCt_bounds _ _
        | _ => simp [hop, harg, h.1, h.2]
    | MERGE =>
        cases harg : (lFetch P s.ip).arg with
        | token act => simp only [hop, harg]; exact applyTokenAction_tokenCt_bounds _ _
        | _ => simp [hop, harg, h.1, h.2]

/-- `lStep` preserves token parity invariant for all opcodes. -/
lemma lStep_preserves_tokenParity (P : LProgram) (s : LState)
  (h : TokenParityInvariant s) : TokenParityInvariant (lStep P s) := by
  unfold TokenParityInvariant at *
  exact lStep_tokenCt_bounds P s h

/-- lStep preserves kPerp: no opcode modifies reg6.kPerp. -/
lemma lStep_kPerp_eq (P : LProgram) (s : LState) :
    (lStep P s).reg6.kPerp = s.reg6.kPerp := by
  by_cases hH : s.halted
  · simp [lStep, hH]
  · simp only [lStep, hH, ↓reduceIte]
    cases hop : (lFetch P s.ip).op <;>
      simp only [hop] <;>
        try rfl
    -- FOLD case: only nuPhi is modified
    all_goals simp only [Reg6.mk.injEq] at *
    all_goals rfl

/-- No opcode in the current semantics mutates `kPerp`, so SU3Invariant is preserved. -/
lemma lStep_preserves_su3 (P : LProgram) (s : LState)
  (h : SU3Invariant s) : SU3Invariant (lStep P s) := by
  unfold SU3Invariant at *
  rw [lStep_kPerp_eq]
  exact h

/-- If a LISTEN instruction with vector-reset mode is issued at end-of-breath,
    the cycle sum resets to zero on the next step. -/
lemma listen_reset_resets_cycleSum (P : LProgram) (s : LState)
  (hRun : s.halted = false)
  (hop : (lFetch P s.ip).op = Opcode.LISTEN)
  (hmode : (lFetch P s.ip).arg = OpcodeArg.listen ListenMode.vectorReset)
  (hEnd : s.breath = breathPeriod - 1) :
  (lStep P s).vecSumCycle = 0 := by
  have hop' : (P s.ip).op = Opcode.LISTEN := by
    simpa [lFetch] using hop
  have hmode' : (P s.ip).arg = OpcodeArg.listen ListenMode.vectorReset := by
    simpa [lFetch] using hmode
  simp [lStep, hRun, hop', hmode', hEnd]

/-- After `BALANCE` at idx=7, the next state has winIdx8=0 and winSum8=0. -/
lemma lStep_balance_resets (P : LProgram) (s : LState)
  (hRun : s.halted = false)
  (hbal : (lFetch P s.ip).op = Opcode.BALANCE)
  (hNotCycle : (lFetch P s.ip).arg ≠ OpcodeArg.balance BalanceMode.cycle)
  (hidx : s.winIdx8 = 7) :
  (lStep P s).winIdx8 = 0 ∧ (lStep P s).winSum8 = 0 := by
  have hop' : (P s.ip).op = Opcode.BALANCE := by
    simpa [lFetch] using hbal
  have hnc : (P s.ip).arg ≠ OpcodeArg.balance BalanceMode.cycle := by
    simpa [lFetch] using hNotCycle
  have hadv0 : (s.winIdx8 + 1) % 8 = 0 := by
    simpa [hidx]
  -- `lStep` splits on the BALANCE arg: the `cycle` branch does not window-reset.
  -- We exclude it via `hNotCycle`, then discharge the window-reset branch by simp.
  cases harg : (P s.ip).arg with
  | balance mode =>
    cases mode with
    | cycle =>
      exfalso
      apply hnc
      simpa [harg]
    | window =>
      simp [lStep, hRun, hop', harg, hidx, hadv0]
  | none =>
      simp [lStep, hRun, hop', harg, hidx, hadv0]
  | fold dir =>
      simp [lStep, hRun, hop', harg, hidx, hadv0]
  | token act =>
      simp [lStep, hRun, hop', harg, hidx, hadv0]
  | listen mode =>
      simp [lStep, hRun, hop', harg, hidx, hadv0]

/-- If the 7th successor state sits at winIdx8=7 and issues BALANCE,
    then after 8 steps the window resets (sum=0, idx=0). -/
lemma neutral_after_8 (P : LProgram) (s : LState)
  (hRun7 : (Function.iterate (lStep P) 7 s).halted = false)
  (hIdx7 : (Function.iterate (lStep P) 7 s).winIdx8 = 7)
  (hBal  : (lFetch P (Function.iterate (lStep P) 7 s).ip).op = Opcode.BALANCE) :
  (lFetch P (Function.iterate (lStep P) 7 s).ip).arg ≠ OpcodeArg.balance BalanceMode.cycle →
  (Function.iterate (lStep P) 8 s).winSum8 = 0 ∧ (Function.iterate (lStep P) 8 s).winIdx8 = 0 := by
  let s7 := Function.iterate (lStep P) 7 s
  intro hNotCycle
  have h := lStep_balance_resets P s7 (by simpa [s7] using hRun7) hBal hNotCycle hIdx7
  -- One more step from s7 is the 8th iterate
  have h' : (lStep P s7).winSum8 = 0 ∧ (lStep P s7).winIdx8 = 0 :=
    ⟨h.2, h.1⟩
  -- Definitional unfolding of `Function.iterate` expands `8` into eight nested steps.
  simpa [Function.iterate, Nat.succ_eq_add_one] using h'

/-- `winIdx8` remains < 8 after one step, assuming it is < 8 initially. -/
lemma lStep_winIdx_lt8 (P : LProgram) (s : LState) (h : s.winIdx8 < 8) :
    (lStep P s).winIdx8 < 8 := by
  unfold lStep
  by_cases hH : s.halted
  · -- halted branch keeps `winIdx8` unchanged
    simpa [hH] using h
  ·
    have hadv : (s.winIdx8 + 1) % 8 < 8 := Nat.mod_lt _ (by decide)
    -- split on opcode; all running branches set `winIdx8` to `(winIdx8+1)%8` or 0
    cases hop : (P s.ip).op with
    | BALANCE =>
      -- In BALANCE mode, `winIdx8` is `advIdx` unless we are at end-of-breath in `cycle` mode.
      cases harg : (P s.ip).arg with
      | balance mode =>
        cases mode with
        | cycle =>
          -- The `cycle` sub-branch forces `winIdx8 := 0` only at `breath = breathPeriod - 1` (i.e., 1023).
          by_cases hb : s.breath = 1023
          · simp [hH, hop, harg, hb]
          · simpa [hH, hop, harg, hb] using hadv
        | window =>
          simp [hH, hop, harg, hadv]
      | none =>
          simp [hH, hop, harg, hadv]
      | fold dir =>
          simp [hH, hop, harg, hadv]
      | token act =>
          simp [hH, hop, harg, hadv]
      | listen mode =>
          simp [hH, hop, harg, hadv]
    | _ =>
      simp [hH, hop, hadv]

/-- Single step: breath advances by 1 mod breathPeriod. -/
lemma lStep_breath_eq (P : LProgram) (s : LState) :
    (lStep P s).breath = (s.breath + 1) % breathPeriod := by
  -- The VM definition ends with `{ core with breath := lBumpBreath core }`
  -- where lBumpBreath core := (core.breath + 1) % breathPeriod.
  -- We show that core.breath = s.breath regardless of the opcode.
  unfold lStep
  dsimp only
  -- The field core.breath is s.breath because none of the updates in lStep modify it.
  -- Instead of unfolding everything, we can use the fact that breath is not modified.
  simp only [lBumpBreath, breathPeriod]
  split
  · -- Case: s.halted = true
    rfl
  · -- Case: s.halted = false
    -- All opcode branches preserve s.breath
    repeat split
    all_goals rfl

/-- Breath position after n steps is (breath + n) % breathPeriod. -/
lemma lStep_breath_after (P : LProgram) (s : LState) (hB : BreathBound s) :
    ∀ n, (Function.iterate (lStep P) n s).breath = (s.breath + n) % breathPeriod := by
  intro n
  induction n with
  | zero =>
      -- base: iterate 0 = identity; use BreathBound to simplify mod
      simpa [Function.iterate_zero, Nat.add_zero] using (Nat.mod_eq_of_lt hB).symm
  | succ n ih =>
      -- step: breath bumps by 1 each iteration
      have hStep :
          Function.iterate (lStep P) (n + 1) s =
            lStep P (Function.iterate (lStep P) n s) :=
        Function.iterate_succ_apply' (lStep P) n s
      rw [hStep]
      -- apply one-step lemma, then IH
      rw [lStep_breath_eq, ih]
      -- Now: ((a % m) + 1) % m = (a + 1) % m, with a = s.breath + n and m = breathPeriod.
      have h1 : 1 % breathPeriod = 1 := by
        -- breathPeriod = 1024, so 1 < breathPeriod.
        exact Nat.mod_eq_of_lt (by decide : 1 < breathPeriod)
      calc
        (((s.breath + n) % breathPeriod) + 1) % breathPeriod
            = (((s.breath + n) % breathPeriod) + (1 % breathPeriod)) % breathPeriod := by
                simpa [h1]
        _   = ((s.breath + n) + 1) % breathPeriod := by
                simpa using (Nat.add_mod (s.breath + n) 1 breathPeriod).symm
        _   = (s.breath + Nat.succ n) % breathPeriod := by
                simp [Nat.succ_eq_add_one, Nat.add_assoc]

/-- After breathPeriod steps, breath returns to initial value (requires BreathBound). -/
lemma lStep_breath_periodic (P : LProgram) (s : LState) (hB : BreathBound s) :
  (Function.iterate (lStep P) breathPeriod s).breath = s.breath := by
  -- Use the closed form and reduce (breath + breathPeriod) % breathPeriod = breath.
  have h := lStep_breath_after P s hB breathPeriod
  -- Now simplify the RHS.
  have hbmod : s.breath % breathPeriod = s.breath := by
    exact Nat.mod_eq_of_lt hB
  calc
    (Function.iterate (lStep P) breathPeriod s).breath
        = (s.breath + breathPeriod) % breathPeriod := h
    _   = (s.breath % breathPeriod + breathPeriod % breathPeriod) % breathPeriod := by
          simpa [Nat.add_mod]
    _   = s.breath % breathPeriod := by simp
    _   = s.breath := hbmod

/-- **Phase 1.1 Quick Win**: Breath arithmetic modulo breathPeriod. -/
theorem breath_modular_add (P : LProgram) (s : LState) (n m : ℕ) (hB : BreathBound s) :
    (Function.iterate (lStep P) (n + m) s).breath =
    ((Function.iterate (lStep P) n s).breath + m) % breathPeriod := by
  -- Re-associate the iterate as: f^[n+m] s = f^[m] (f^[n] s).
  have hIter :
      Function.iterate (lStep P) (n + m) s =
        Function.iterate (lStep P) m (Function.iterate (lStep P) n s) := by
    -- `iterate_add_apply` is for `(m + n)`; rewrite the sum first.
    simpa [Nat.add_comm] using (Function.iterate_add_apply (lStep P) m n s)
  -- Use `lStep_breath_after` on the state after `n` steps.
  have hBn : BreathBound (Function.iterate (lStep P) n s) := by
    induction n with
    | zero => exact hB
    | succ n ih =>
        have hStep :
            Function.iterate (lStep P) (n + 1) s =
              lStep P (Function.iterate (lStep P) n s) :=
          Function.iterate_succ_apply' (lStep P) n s
        -- `iterate (succ n)` is definitionally `iterate (n+1)` up to `Nat.succ_eq_add_one`.
        simpa [Nat.succ_eq_add_one, hStep]
          using (preservation_breath P (Function.iterate (lStep P) n s))
  -- Now apply the closed form on the tail state.
  simpa [hIter] using (lStep_breath_after P (Function.iterate (lStep P) n s) hBn m)

/-- **Phase 1.1 Quick Win**: A full breath cycle returns the clock to its start. -/
theorem breath_cycle_complete (P : LProgram) (s : LState) (hB : BreathBound s) :
    (Function.iterate (lStep P) breathPeriod s).breath = s.breath :=
  lStep_breath_periodic P s hB

/-- Eight‑tick invariant bundle (scheduler assumptions + base alignment). -/
structure EightTickInvariant (P : LProgram) (s : LState) : Prop where
  aligned : alignedBoundaries P s
  balanceAt7 : balanceWhenIdx7 P s
  baseIdx0 : s.winIdx8 = 0
  baseIdxLt : s.winIdx8 < 8
  baseSum0 : s.winSum8 = 0
  runAll : ∀ k, (Function.iterate (lStep P) k s).halted = false

/-- Under the eight‑tick invariant bundle, every 8‑step boundary is neutral. -/
theorem eightTick_neutral_all (P : LProgram) {s : LState}
  (H : EightTickInvariant P s) :
  ∀ k, (Function.iterate (lStep P) (8 * k) s).winIdx8 = 0
       ∧ (Function.iterate (lStep P) (8 * k) s).winSum8 = 0 := by
  intro k
  exact neutral_every_8th_from0 P s H.baseIdxLt H.aligned H.balanceAt7 H.baseIdx0 H.baseSum0 H.runAll k

/-- `balanceWhenIdx7` is stable under time-rotation (iteration). -/
lemma balanceWhenIdx7_shift (P : LProgram) (s : LState)
  (h : balanceWhenIdx7 P s) (n : Nat) :
  balanceWhenIdx7 P (Function.iterate (lStep P) n s) := by
  intro t hIdx
  -- f^[t] (f^[n] s) = f^[n + t] s by iterate_add_apply with swapped order
  have hEq : Function.iterate (lStep P) t (Function.iterate (lStep P) n s) =
             Function.iterate (lStep P) (n + t) s := by
    have := Function.iterate_add_apply (lStep P) t n s
    simp only [Nat.add_comm t n] at this
    exact this.symm
  -- Apply the original hypothesis at time n + t
  have hIdx' : (Function.iterate (lStep P) (n + t) s).winIdx8 = 7 := by
    rw [← hEq]; exact hIdx
  have hResult := h (n + t) hIdx'
  -- Rewrite back to the shifted form using congruence
  simp only [← hEq] at hResult
  exact hResult

/-- There exists a rotation ≤7 steps that lands at window index 0 (under alignment).

    Requires `hIdx : s.winIdx8 < 8` and `hRunAll` to use the advance lemma. -/
lemma exists_rotation_to_idx0 (P : LProgram) (s : LState)
  (hIdx : s.winIdx8 < 8)
  (hA : alignedBoundaries P s)
  (hRunAll : ∀ k, (Function.iterate (lStep P) k s).halted = false) :
  ∃ r, r ≤ 7 ∧ (Function.iterate (lStep P) r s).winIdx8 = 0 := by
  -- Choose r = (8 - s.winIdx8) % 8
  -- If s.winIdx8 = 0, then r = 0; otherwise r = 8 - s.winIdx8
  let r := (8 - s.winIdx8) % 8
  use r
  constructor
  · -- r ≤ 7
    exact Nat.lt_succ_iff.mp (Nat.mod_lt (8 - s.winIdx8) (by decide : 0 < 8))
  · -- (f^r s).winIdx8 = 0
    have hAdvance := winIdx8_after_n_aligned P s hIdx hA hRunAll r
    rw [hAdvance]
    -- Goal: (s.winIdx8 + r) % 8 = 0
    -- r = (8 - s.winIdx8) % 8
    -- s.winIdx8 + (8 - s.winIdx8) % 8 ≡ 0 (mod 8) when s.winIdx8 < 8
    by_cases h0 : s.winIdx8 = 0
    · simp [h0, r]
    · -- s.winIdx8 ∈ {1..7}, so r = 8 - s.winIdx8 ∈ {1..7}
      have hPos : 0 < s.winIdx8 := Nat.pos_of_ne_zero h0
      have hLe7 : s.winIdx8 ≤ 7 := Nat.lt_succ_iff.mp hIdx
      have hr : r = 8 - s.winIdx8 := by
        simp only [r, Nat.mod_eq_of_lt]
        omega
      rw [hr]
      -- s.winIdx8 + (8 - s.winIdx8) = 8
      have hSum : s.winIdx8 + (8 - s.winIdx8) = 8 := by omega
      simp [hSum]

/-- Schedule neutrality is invariant under rotation: there exists r≤7 such that
    neutrality holds at times r + 8k for all k. -/
theorem schedule_neutrality_rotation (P : LProgram) {s : LState}
  (H : EightTickInvariant P s) :
  ∃ r, r ≤ 7 ∧ ∀ k,
    (Function.iterate (lStep P) (r + 8 * k) s).winIdx8 = 0 ∧
    (Function.iterate (lStep P) (r + 8 * k) s).winSum8 = 0 := by
  -- Since H.baseIdx0 : s.winIdx8 = 0, we use r = 0 and apply neutral_every_8th_from0
  use 0
  constructor
  · decide
  · intro k
    simp only [Nat.zero_add]
    exact neutral_every_8th_from0 P s H.baseIdxLt H.aligned H.balanceAt7 H.baseIdx0 H.baseSum0 H.runAll k

/-! ## Window Cost Ceiling (|GIVE−REGIVE| ≤ 4 per 8‑tick window) -/

/-- Define the 8‑tick window cost at step n as the accumulator `winSum8` observed
    at that step. Under the eight‑tick scheduler invariants, this value is 0 at
    window boundaries (and at a suitable rotation `r ≤ 7`). -/
@[simp] def windowCostAt (P : LProgram) (s : LState) (n : Nat) : Int :=
  (Function.iterate (lStep P) n s).winSum8

/-- Cost ceiling at window boundaries: absolute cost ≤ 4 (in fact 0) for all k. -/
theorem cost_ceiling_window_boundaries (P : LProgram) {s : LState}
  (H : EightTickInvariant P s) :
  ∀ k, Int.abs (windowCostAt P s (8 * k)) ≤ 4 := by
  intro k
  -- From `eightTick_neutral_all`, window sum is 0 at boundaries
  have h := eightTick_neutral_all P (s := s) H k
  have hsum : (Function.iterate (lStep P) (8 * k) s).winSum8 = 0 := h.right
  simpa [windowCostAt, hsum]

/-! ### Rotated neutrality and bundled consequences -/

/-- From alignment, balancing at idx=7, and base idx=0, neutrality holds at a
    rotation `r ≤ 7` across all 8‑step boundaries. This packages the existing
    schedule lemmas into a single convenient statement. -/
theorem rotated_neutrality_from_aligned_balance_base (P : LProgram) {s : LState}
  (hA : alignedBoundaries P s) (hBal : balanceWhenIdx7 P s)
  (h0 : s.winIdx8 = 0) (hIdxLt : s.winIdx8 < 8) (hSum0 : s.winSum8 = 0)
  (hRunAll : ∀ k, (Function.iterate (lStep P) k s).halted = false) :
  ∃ r, r ≤ 7 ∧ ∀ k,
    (Function.iterate (lStep P) (r + 8 * k) s).winIdx8 = 0 ∧
    (Function.iterate (lStep P) (r + 8 * k) s).winSum8 = 0 := by
  have H : EightTickInvariant P s := {
    aligned := hA, balanceAt7 := hBal, baseIdx0 := h0,
    baseIdxLt := hIdxLt, baseSum0 := hSum0, runAll := hRunAll
  }
  simpa using (schedule_neutrality_rotation (P:=P) (s:=s) H)

-- Cost ceiling bundle: both boundary and rotated boundary versions follow
-- immediately from `EightTickInvariant` (see `cost_ceiling_all` below).
-- NOTE: We intentionally avoid a long-run “every step” lemma here for now.
-- The single-step δ-unit lemma (`token_delta_unit`) is the stable interface
-- used by certificates; iterated variants can be added once the VM budget
-- layer is finalized.

/-- Convenience: neutrality at every base boundary from the bundle. -/
theorem boundary_neutrality_from_invariant (P : LProgram) {s : LState}
  (H : EightTickInvariant P s) :
  ∀ k, (Function.iterate (lStep P) (8 * k) s).winIdx8 = 0
       ∧ (Function.iterate (lStep P) (8 * k) s).winSum8 = 0 := by
  simpa using (eightTick_neutral_all (P:=P) (s:=s) H)

/-- Cost ceiling at a rotated boundary: there exists r ≤ 7 such that
    for all k, the window starting at n = r + 8k has cost 0 (hence ≤ 4). -/
theorem cost_ceiling_window_rotated (P : LProgram) {s : LState}
  (H : EightTickInvariant P s) :
  ∃ r, r ≤ 7 ∧ ∀ k, Int.abs (windowCostAt P s (r + 8 * k)) ≤ 4 := by
  rcases schedule_neutrality_rotation (P:=P) (s:=s) H with ⟨r, hr, h⟩
  refine ⟨r, hr, ?bound⟩
  intro k
  have hsum : (Function.iterate (lStep P) (r + 8 * k) s).winSum8 = 0 := (h k).right
  simpa [windowCostAt, hsum]

/-- Cost ceiling bundle: both boundary and rotated-boundary versions follow
    immediately from `EightTickInvariant`. -/
theorem cost_ceiling_all (P : LProgram) {s : LState} (H : EightTickInvariant P s) :
  (∀ k, Int.abs (windowCostAt P s (8 * k)) ≤ 4)
  ∧ (∃ r, r ≤ 7 ∧ ∀ k, Int.abs (windowCostAt P s (r + 8 * k)) ≤ 4) := by
  refine And.intro ?hb ?hr
  · intro k; simpa using (cost_ceiling_window_boundaries (P:=P) (s:=s) H k)
  · simpa using (cost_ceiling_window_rotated (P:=P) (s:=s) H)

/-- Bundled VM invariant used for preservation/progress. -/
def VMInvariant (s : LState) : Prop :=
  BreathBound s ∧ (s.winIdx8 < 8) ∧ TokenParityInvariant s ∧ SU3Invariant s

/-- lStep preserves the bundled VM invariant. -/
lemma lStep_preserves_VMInvariant (P : LProgram) (s : LState)
  (h : VMInvariant s) : VMInvariant (lStep P s) := by
  rcases h with ⟨hBreath, hIdx, hTok, hSU3⟩
  refine And.intro ?hb (And.intro ?hi (And.intro ?ht ?hs))
  · -- breath bound preservation
    simpa [BreathBound] using (preservation_breath P s)
  · -- winIdx8 < 8
    simpa using (lStep_winIdx_lt8 P s hIdx)
  · -- token parity preserved
    simpa using (lStep_preserves_tokenParity P s hTok)
  · -- SU(3) preserved
    simpa using (lStep_preserves_su3 P s hSU3)

/-! ## Eight‑step cycle and preservation -/

/-- Define one window cycle as eight successive `lStep`s. -/
def lCycle (P : LProgram) (s : LState) : LState :=
  Function.iterate (lStep P) 8 s

/-- `lStep^[n]` preserves the bundled VM invariant. -/
lemma lStep_iterate_preserves_VMInvariant (P : LProgram) (s : LState) (n : Nat)
  (h : VMInvariant s) : VMInvariant (Function.iterate (lStep P) n s) := by
  induction n with
  | zero => exact h
  | succ n ih =>
      have hEq : Function.iterate (lStep P) (n + 1) s =
                 lStep P (Function.iterate (lStep P) n s) :=
        Function.iterate_succ_apply' (lStep P) n s
      rw [hEq]
      exact lStep_preserves_VMInvariant P _ ih

/-- `lCycle` preserves the bundled VM invariant (by eight applications of the step lemma). -/
lemma lCycle_preserves_VMInvariant (P : LProgram) (s : LState)
  (h : VMInvariant s) : VMInvariant (lCycle P s) := by
  unfold lCycle
  exact lStep_iterate_preserves_VMInvariant P s 8 h

/-- Progress: every state can take a relational small‑step. -/
theorem VM_progress (P : LProgram) (s : LState) : ∃ s', LStepRel P s s' :=
  progress P s

/-- Unit‑delta predicate for integer counters. -/
def DeltaUnit (x y : Int) : Prop := Int.abs (y - x) ≤ 1

/-- Token count changes by at most one per `lStep` when parity holds. -/
lemma token_delta_unit (P : LProgram) (s : LState)
  (hTok : TokenParityInvariant s) :
  DeltaUnit s.aux5.tokenCt (lStep P s).aux5.tokenCt := by
  unfold DeltaUnit
  set x : Int := s.aux5.tokenCt
  set y : Int := (lStep P s).aux5.tokenCt

  have hx0 : 0 ≤ x := by simpa [x] using hTok.1
  have hx1 : x ≤ 1 := by simpa [x] using hTok.2

  have hTok' : TokenParityInvariant (lStep P s) :=
    lStep_preserves_tokenParity (P := P) (s := s) hTok
  have hy0 : 0 ≤ y := by simpa [y] using hTok'.1
  have hy1 : y ≤ 1 := by simpa [y] using hTok'.2

  have hdiff_le : y - x ≤ (1 : Int) := by
    have hnegx : -x ≤ 0 := neg_nonpos.mpr hx0
    have h2 : y - x ≤ y := by
      have : y + (-x) ≤ y + 0 := by linarith
      simpa [sub_eq_add_neg] using this
    exact le_trans h2 hy1

  have hdiff_ge : (-1 : Int) ≤ y - x := by
    have hneg1 : (-1 : Int) ≤ -x := by
      -- From `x ≤ 1`, negate both sides.
      simpa using (neg_le_neg hx1)
    have hnegx_le : -x ≤ y - x := by
      have h : (0 : Int) + (-x) ≤ y + (-x) := by linarith
      simpa [sub_eq_add_neg, zero_add] using h
    exact le_trans hneg1 hnegx_le

  have habs : |y - x| ≤ (1 : Int) :=
    abs_le.mpr ⟨by simpa using hdiff_ge, by simpa using hdiff_le⟩

  have habsEq : Int.abs (y - x) = |y - x| := by
    -- `Int.abs` is our `Int → Int` wrapper; it coincides with `|·|` on `ℤ`.
    simpa [Int.abs] using (Int.natCast_natAbs (y - x))

  have : Int.abs (y - x) ≤ (1 : Int) := by
    -- Rewrite to the standard absolute value on `ℤ`.
    rw [habsEq]
    exact habs

  simpa [x, y] using this

end LNAL
end IndisputableMonolith
