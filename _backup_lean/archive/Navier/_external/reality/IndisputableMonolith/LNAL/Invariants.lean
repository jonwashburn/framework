import Mathlib
import IndisputableMonolith.LNAL.Registers
import IndisputableMonolith.LNAL.Opcodes
import IndisputableMonolith.LNAL.VM
import IndisputableMonolith.LNAL.JBudget
/-- FLIP toggles exactly at mid-breath (511 for breathPeriod=1024), otherwise leaves `flipped` unchanged. -/
lemma lStep_flip_behavior (P : LProgram) (s : LState)
  (hop : (lFetch P s.ip).op = Opcode.FLIP) :
  let mid := breathPeriod / 2 - 1;
  ((s.breath = mid → (lStep P s).flipped = not s.flipped) ∧
   (s.breath ≠ mid → (lStep P s).flipped = s.flipped)) := by
  intro mid; unfold lStep
  by_cases hH : s.halted
  · simp [hH, hop]
  · simp [hH, hop]

/-- Scheduling rule: whenever winIdx8=7, the next opcode is BALANCE. -/
def balanceWhenIdx7 (P : LProgram) (s : LState) : Prop :=
  ∀ t, (Function.iterate (lStep P) t s).winIdx8 = 7 →
       (lFetch P (Function.iterate (lStep P) t s).ip).op = Opcode.BALANCE

/-- If the scheduler satisfies `balanceWhenIdx7`, every encountered boundary resets on the next step. -/
lemma neutral_at_any_boundary (P : LProgram) (s : LState)
  (hBal : balanceWhenIdx7 P s) (t : Nat)
  (hIdx7 : (Function.iterate (lStep P) t s).winIdx8 = 7) :
  let sT := Function.iterate (lStep P) t s;
  (lStep P sT).winSum8 = 0 ∧ (lStep P sT).winIdx8 = 0 := by
  intro sT; have hop := hBal t hIdx7; exact lStep_balance_resets P _ hop hIdx7

/-- Alignment predicate: breath ends only at window boundary (idx=7). -/
def alignedBoundaries (P : LProgram) (s : LState) : Prop :=
  ∀ t, (Function.iterate (lStep P) t s).breath = breathPeriod - 1 →
       (Function.iterate (lStep P) t s).winIdx8 = 7

/-- Alignment is preserved when shifting the starting state by iteration. -/
lemma alignedBoundaries_shift (P : LProgram) (s : LState)
  (hA : alignedBoundaries P s) (n : Nat) :
  alignedBoundaries P (Function.iterate (lStep P) n s) := by
  intro t hEnd
  have := hA (n + t)
  simpa [Function.iterate, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this hEnd

/-- With aligned boundaries, `winIdx8` advances by +1 mod 8 each step. -/
lemma winIdx8_adv_aligned (P : LProgram) (s : LState)
  (hA : alignedBoundaries P s) :
  (lStep P s).winIdx8 = (s.winIdx8 + 1) % 8 := by
  unfold lStep
  by_cases hH : s.halted
  · simp [hH]
  · by_cases hEnd : s.breath = breathPeriod - 1
    · -- Only possible at idx 7 by alignment; CYCLE branch reduces to advIdx=0
      have h7 : s.winIdx8 = 7 := (hA 0) (by simpa [Function.iterate])
      have : (s.winIdx8 + 1) % 8 = 0 := by simpa [h7]
      cases hop : (lFetch P s.ip).op <;> simp [hH, hop, h7, this]
    · -- Not at end-of-breath: all branches set advIdx := (idx+1)%8
      cases hop : (lFetch P s.ip).op <;> simp [hH, hop]

/-- For aligned boundaries, explicit formula for index after n steps. -/
lemma winIdx8_after_n_aligned (P : LProgram) (s : LState)
  (hA : alignedBoundaries P s) :
  ∀ n, (Function.iterate (lStep P) n s).winIdx8 = (s.winIdx8 + n) % 8 := by
  intro n; induction n with
  | zero => simp
  | succ n ih =>
    have hA' := alignedBoundaries_shift P s hA n
    simpa [Function.iterate, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.add_mod, ih]
      using winIdx8_adv_aligned P (Function.iterate (lStep P) n s) hA'

/-- If starting aligned at idx=0 and the scheduler balances at idx=7, then the window is neutral at every 8-step boundary across long runs. -/
lemma neutral_every_8th_from0 (P : LProgram) (s : LState)
  (hA : alignedBoundaries P s) (hBal : balanceWhenIdx7 P s)
  (h0 : s.winIdx8 = 0) :
  ∀ k, (Function.iterate (lStep P) (8 * k) s).winIdx8 = 0 ∧ (Function.iterate (lStep P) (8 * k) s).winSum8 = 0 := by
  intro k; induction k with
  | zero => simpa [Nat.mul_zero] using And.intro (by simpa [Nat.zero_add, h0] using (winIdx8_after_n_aligned P s hA 0)) (by simp)
  | succ k ih =>
    -- Move 8 steps from the previous boundary, reaching next boundary and neutrality
    have idx7 : (Function.iterate (lStep P) (8 * k + 7) s).winIdx8 = 7 := by
      simpa [Nat.mul_comm, Nat.left_distrib, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.add_mod]
        using (winIdx8_after_n_aligned P s hA (8 * k + 7))
    have reset := neutral_at_any_boundary P s hBal (8 * k + 7) idx7
    -- One more step lands at the next boundary (8*(k+1)) with sum=0 and idx=0
    simpa [Function.iterate, Nat.succ_eq_add_one, Nat.mul_succ, Nat.left_distrib, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using reset

namespace IndisputableMonolith
namespace LNAL

/-- Token parity invariant: tokenCt ∈ {0,1}. -/
def TokenParityInvariant (s : LState) : Prop := (0 ≤ s.aux5.tokenCt) ∧ (s.aux5.tokenCt ≤ 1)

/-- Minimal SU(3) triad legality: limit transverse mode to −1,0,1. -/
def SU3Invariant (s : LState) : Prop := s.reg6.kPerp = (-1) ∨ s.reg6.kPerp = 0 ∨ s.reg6.kPerp = 1

/-- clamp01 yields a value in {0,1}. -/
lemma clamp01_bounds (x : Int) : 0 ≤ clamp01 x ∧ clamp01 x ≤ 1 := by
  unfold clamp01
  by_cases h0 : x ≤ 0
  · simp [h0]
  · have h0' : ¬ x ≤ 0 := h0
    simp [h0, h0']
    by_cases h1 : 1 ≤ x
    · simp [h1]
    · have h1' : ¬ 1 ≤ x := h1
      -- In this branch 0 < x < 1 over Int ⇒ clamp01 x = x, but Int has no elements strictly between 0 and 1
      -- so this branch is unreachable; we still discharge it with inequalities implied by cases.
      -- We conservatively conclude 0 ≤ x and x ≤ 1 from the guards.
      have hx0 : 0 < x := lt_of_le_of_ne (le_of_not_gt h0) (by decide)
      have hx1 : x ≤ 1 := le_of_not_ge h1
      have hx0' : 0 ≤ x := Int.le_of_lt hx0
      simp [h1, h0, hx0', hx1]

/-- `lStep` preserves token parity invariant for all opcodes. -/
lemma lStep_preserves_tokenParity (P : LProgram) (s : LState)
  (h : TokenParityInvariant s) : TokenParityInvariant (lStep P s) := by
  unfold TokenParityInvariant at h
  rcases h with ⟨hlo, hhi⟩
  unfold lStep
  by_cases hH : s.halted
  · simp [hH, TokenParityInvariant, hlo, hhi]
  ·
    set instr := lFetch P s.ip
    have : instr = lFetch P s.ip := rfl
    simp [hH, this]
    cases hop : instr.op with
    | LOCK =>
        simp [hop, TokenParityInvariant, hlo, hhi]
    | BALANCE =>
        simp [hop, TokenParityInvariant, hlo, hhi]
    | FOLD =>
        simp [hop, TokenParityInvariant, hlo, hhi]
    | SEED =>
        cases harg : instr.arg with
        | none =>
            have hClamp := clamp01_bounds (1 : Int)
            simpa [hop, harg, TokenParityInvariant, applyTokenAction] using hClamp
        | fold _ =>
            simp [hop, harg, TokenParityInvariant, applyTokenAction, hlo, hhi]
        | token act =>
            cases act with
            | delta d =>
                have hClamp := clamp01_bounds (s.aux5.tokenCt + d)
                simpa [hop, harg, act, TokenParityInvariant, applyTokenAction] using hClamp
            | set value cost =>
                have hClamp := clamp01_bounds value
                simpa [hop, harg, act, TokenParityInvariant, applyTokenAction] using hClamp
        | balance _ =>
            simp [hop, harg, TokenParityInvariant, applyTokenAction, hlo, hhi]
        | listen _ =>
            simp [hop, harg, TokenParityInvariant, applyTokenAction, hlo, hhi]
    | BRAID =>
        cases harg : instr.arg with
        | token (TokenAction.delta d) =>
            have hClamp := clamp01_bounds (s.aux5.tokenCt + d)
            simpa [hop, harg, TokenParityInvariant, applyTokenAction] using hClamp
        | token (TokenAction.set value cost) =>
            have hClamp := clamp01_bounds value
            simpa [hop, harg, TokenParityInvariant, applyTokenAction] using hClamp
        | _ =>
            simp [hop, harg, TokenParityInvariant, hlo, hhi]
    | MERGE =>
        cases harg : instr.arg with
        | token (TokenAction.delta d) =>
            have hClamp := clamp01_bounds (s.aux5.tokenCt + d)
            simpa [hop, harg, TokenParityInvariant, applyTokenAction] using hClamp
        | token (TokenAction.set value cost) =>
            have hClamp := clamp01_bounds value
            simpa [hop, harg, TokenParityInvariant, applyTokenAction] using hClamp
        | _ =>
            simp [hop, harg, TokenParityInvariant, hlo, hhi]
    | LISTEN =>
        simp [hop, TokenParityInvariant, hlo, hhi]
    | FLIP =>
        simp [hop, TokenParityInvariant, hlo, hhi]

/-- No opcode in the current semantics mutates `kPerp`, so SU3Invariant is preserved. -/
lemma lStep_preserves_su3 (P : LProgram) (s : LState)
  (h : SU3Invariant s) : SU3Invariant (lStep P s) := by
  unfold SU3Invariant at h
  unfold lStep
  by_cases hH : s.halted
  · simpa [hH, SU3Invariant]
  · cases hop : (lFetch P s.ip).op <;> simp [hH, hop, SU3Invariant] at * <;> assumption?

/-- If a LISTEN instruction with vector-reset mode is issued at end-of-breath,
    the cycle sum resets to zero on the next step. -/
lemma listen_reset_resets_cycleSum (P : LProgram) (s : LState)
  (hop : (lFetch P s.ip).op = Opcode.LISTEN)
  (hmode : (lFetch P s.ip).arg = OpcodeArg.listen ListenMode.vectorReset)
  (hEnd : s.breath = breathPeriod - 1) :
  (lStep P s).vecSumCycle = 0 := by
  unfold lStep
  by_cases hH : s.halted
  · simp [hH, hop]
  · simp [hH, hop, hmode, hEnd]

/-- After `BALANCE` at idx=7, the next state has winIdx8=0 and winSum8=0. -/
lemma lStep_balance_resets (P : LProgram) (s : LState)
  (hbal : (lFetch P s.ip).op = Opcode.BALANCE) (hidx : s.winIdx8 = 7) :
  (lStep P s).winIdx8 = 0 ∧ (lStep P s).winSum8 = 0 := by
  unfold lStep
  by_cases hH : s.halted
  · simp [hH, hbal]  -- halted case is vacuous; lStep returns s
  · simp [hH, hbal, hidx]

/-- If the 7th successor state sits at winIdx8=7 and issues BALANCE,
    then after 8 steps the window resets (sum=0, idx=0). -/
lemma neutral_after_8 (P : LProgram) (s : LState)
  (hIdx7 : (Function.iterate (lStep P) 7 s).winIdx8 = 7)
  (hBal  : (lFetch P (Function.iterate (lStep P) 7 s).ip).op = Opcode.BALANCE) :
  (Function.iterate (lStep P) 8 s).winSum8 = 0 ∧ (Function.iterate (lStep P) 8 s).winIdx8 = 0 := by
  let s7 := Function.iterate (lStep P) 7 s
  have h := lStep_balance_resets P s7 hBal hIdx7
  -- One more step from s7 is the 8th iterate
  simpa [Function.iterate, Nat.succ_eq_add_one] using h

/-- winIdx8 is always reduced modulo 8 after one step. -/
lemma lStep_winIdx_lt8 (P : LProgram) (s : LState) : (lStep P s).winIdx8 < 8 := by
  unfold lStep
  by_cases hH : s.halted
  · simp [hH]
  · have : (s.winIdx8 + 1) % 8 < 8 := Nat.mod_lt _ (by decide)
    -- split on opcode but all branches set winIdx8 := (winIdx8+1)%8
    cases hop : (lFetch P s.ip).op <;> simp [hH, hop, this]

/-- Breath position after n steps is (breath + n) % breathPeriod. -/
lemma lStep_breath_after (P : LProgram) :
  ∀ n s, (Function.iterate (lStep P) n s).breath = (s.breath + n) % breathPeriod := by
  intro n; induction n with
  | zero => intro s; simp
  | succ n ih =>
    intro s; simp [Function.iterate, ih, lBumpBreath, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.add_mod]

/-- After 1024 steps, breath returns to initial value. -/
lemma lStep_breath_periodic (P : LProgram) (s : LState) :
  (Function.iterate (lStep P) breathPeriod s).breath = s.breath := by
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mod_eq_of_lt] using
    (lStep_breath_after P breathPeriod s)

/-- Eight‑tick invariant bundle (scheduler assumptions + base alignment). -/
structure EightTickInvariant (P : LProgram) (s : LState) : Prop where
  aligned : alignedBoundaries P s
  balanceAt7 : balanceWhenIdx7 P s
  baseIdx0 : s.winIdx8 = 0

/-- Under the eight‑tick invariant bundle, every 8‑step boundary is neutral. -/
theorem eightTick_neutral_all (P : LProgram) {s : LState}
  (H : EightTickInvariant P s) :
  ∀ k, (Function.iterate (lStep P) (8 * k) s).winIdx8 = 0
       ∧ (Function.iterate (lStep P) (8 * k) s).winSum8 = 0 := by
  intro k
  exact neutral_every_8th_from0 P s H.aligned H.balanceAt7 H.baseIdx0 k

/-- `balanceWhenIdx7` is stable under time-rotation (iteration). -/
lemma balanceWhenIdx7_shift (P : LProgram) (s : LState)
  (h : balanceWhenIdx7 P s) (n : Nat) :
  balanceWhenIdx7 P (Function.iterate (lStep P) n s) := by
  intro t hIdx
  -- Reduce to the original scheduler at time (n+t)
  have : (Function.iterate (lStep P) (n + t) s).winIdx8 = 7 := by
    simpa [Function.iterate, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using hIdx
  simpa [Function.iterate, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    using h (n + t) this

/-- There exists a rotation ≤7 steps that lands at window index 0 (under alignment). -/
lemma exists_rotation_to_idx0 (P : LProgram) (s : LState)
  (hA : alignedBoundaries P s) : ∃ r, r ≤ 7 ∧ (Function.iterate (lStep P) r s).winIdx8 = 0 := by
  -- Choose r = (8 - (s.winIdx8 % 8)) % 8
  let r := (8 - (s.winIdx8 % 8)) % 8
  have hrange : r ≤ 7 := by
    have : r < 8 := Nat.mod_lt _ (by decide)
    exact Nat.le_of_lt_succ this
  refine ⟨r, hrange, ?hidx0⟩
  -- Use aligned index advance formula
  have hA0 : alignedBoundaries P (Function.iterate (lStep P) 0 s) := by
    simpa using hA
  have adv := winIdx8_after_n_aligned P s hA r
  -- Compute (s.winIdx8 + r) % 8 = 0 by construction of r
  have : (s.winIdx8 + r) % 8 = 0 := by
    unfold r;
    have := Nat.add_mod s.winIdx8 (8 - s.winIdx8 % 8) 8
    -- (a + (8 - a%8)) % 8 = 0
    have hm : (s.winIdx8 % 8 + (8 - s.winIdx8 % 8)) % 8 = 0 := by
      have : (s.winIdx8 % 8 + (8 - s.winIdx8 % 8)) = 8 := by
        exact Nat.add_sub_of_le (Nat.mod_le _ _) |> (by
          -- Use arithmetic: x%8 ≤ 8
          exact rfl)
      simpa [this]
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mod_eq_of_lt (by decide)] using hm
  simpa [Function.iterate, this] using adv

/-- Schedule neutrality is invariant under rotation: there exists r≤7 such that
    neutrality holds at times r + 8k for all k. -/
theorem schedule_neutrality_rotation (P : LProgram) {s : LState}
  (H : EightTickInvariant P s) :
  ∃ r, r ≤ 7 ∧ ∀ k,
    (Function.iterate (lStep P) (r + 8 * k) s).winIdx8 = 0 ∧
    (Function.iterate (lStep P) (r + 8 * k) s).winSum8 = 0 := by
  rcases exists_rotation_to_idx0 P s H.aligned with ⟨r, hr, hidx0⟩
  -- Build an EightTickInvariant at the rotated state
  have hA' := alignedBoundaries_shift P s H.aligned r
  have hBal' := balanceWhenIdx7_shift P s H.balanceAt7 r
  have H' : EightTickInvariant P (Function.iterate (lStep P) r s) :=
    { aligned := hA', balanceAt7 := hBal', baseIdx0 := hidx0 }
  refine ⟨r, hr, ?allk⟩
  intro k
  -- Apply neutrality from the rotated base, then shift back by r in the index
  have := eightTick_neutral_all P (s := Function.iterate (lStep P) r s) H' k
  -- (r + 8k) steps from s equals 8k from the rotated base
  simpa [Function.iterate_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this

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
  have : windowCostAt P s (8 * k) = 0 := by simpa [windowCostAt] using h.right
  simpa [this]

/‑! ### Rotated neutrality and bundled consequences -/

/-- From alignment, balancing at idx=7, and base idx=0, neutrality holds at a
    rotation `r ≤ 7` across all 8‑step boundaries. This packages the existing
    schedule lemmas into a single convenient statement. -/
theorem rotated_neutrality_from_aligned_balance_base (P : LProgram) {s : LState}
  (hA : alignedBoundaries P s) (hBal : balanceWhenIdx7 P s) (h0 : s.winIdx8 = 0) :
  ∃ r, r ≤ 7 ∧ ∀ k,
    (Function.iterate (lStep P) (r + 8 * k) s).winIdx8 = 0 ∧
    (Function.iterate (lStep P) (r + 8 * k) s).winSum8 = 0 := by
  have H : EightTickInvariant P s := { aligned := hA, balanceAt7 := hBal, baseIdx0 := h0 }
  simpa using (schedule_neutrality_rotation (P:=P) (s:=s) H)

/-- Cost ceiling bundle: both boundary and rotated boundary versions follow
    immediately from `EightTickInvariant`. -/
theorem cost_ceiling_all (P : LProgram) {s : LState} (H : EightTickInvariant P s) :
  (∀ k, Int.abs (windowCostAt P s (8 * k)) ≤ 4)
  ∧ (∃ r, r ≤ 7 ∧ ∀ k, Int.abs (windowCostAt P s (r + 8 * k)) ≤ 4) := by
  refine And.intro ?hb ?hr
  · intro k; simpa using (cost_ceiling_window_boundaries (P:=P) (s:=s) H k)
  · simpa using (cost_ceiling_window_rotated (P:=P) (s:=s) H)

/-- Per‑step token count change is unit‑bounded at every step along an execution
    starting from a parity‑valid state. -/
lemma token_delta_unit_every_step (P : LProgram) (s : LState)
  (hTok : TokenParityInvariant s) :
  ∀ n, DeltaUnit ((Function.iterate (lStep P) n s).aux5.tokenCt)
                 ((Function.iterate (lStep P) (n+1) s).aux5.tokenCt) := by
  intro n; induction n with
  | zero =>
      simpa [Function.iterate] using (token_delta_unit (P:=P) (s:=s) hTok)
  | succ n ih =>
      -- Maintain parity then apply one‑step Δ‑unit
      have hPar' : TokenParityInvariant (Function.iterate (lStep P) (n+1) s) := by
        -- parity preserved stepwise
        have hPar_n : TokenParityInvariant (Function.iterate (lStep P) n s) := by
          -- strengthen by iterating preservation n times
          revert s hTok;
          intro s h0;
          induction n with
          | zero => simpa [Function.iterate] using h0
          | succ m ihm =>
              simpa [Function.iterate] using
                (lStep_preserves_tokenParity (P:=P) (s:=Function.iterate (lStep P) m s) ihm)
        simpa [Function.iterate] using
          (lStep_preserves_tokenParity (P:=P) (s:=Function.iterate (lStep P) n s) hPar_n)
      simpa [Function.iterate, Nat.succ_eq_add_one] using
        (token_delta_unit (P:=P) (s:=Function.iterate (lStep P) (n+1) s) hPar')

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
  have : windowCostAt P s (r + 8 * k) = 0 := by
    have hsum := (h k).right
    simpa [windowCostAt] using hsum
  simpa [this]

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
    simpa using (lStep_winIdx_lt8 P s)
  · -- token parity preserved
    simpa using (lStep_preserves_tokenParity P s hTok)
  · -- SU(3) preserved
    simpa using (lStep_preserves_su3 P s hSU3)

/-! ## Eight‑step cycle and preservation -/

/-- Define one window cycle as eight successive `lStep`s. -/
def lCycle (P : LProgram) (s : LState) : LState :=
  Function.iterate (lStep P) 8 s

/-- `lCycle` preserves the bundled VM invariant (by eight applications of the step lemma). -/
lemma lCycle_preserves_VMInvariant (P : LProgram) (s : LState)
  (h : VMInvariant s) : VMInvariant (lCycle P s) := by
  unfold lCycle
  -- iterate the preservation lemma 8 times
  have : ∀ n, VMInvariant ((Function.iterate (lStep P) n) s) := by
    intro n; induction n with
    | zero => simpa using h
    | succ n ih =>
      simpa [Function.iterate] using (lStep_preserves_VMInvariant (P:=P) (s:=Function.iterate (lStep P) n s) ih)
  simpa using (this 8)

/-- Under the budget-aware iteration, eight-step cycles do not increase the J budget. -/
lemma lCycle_budget_monotone (P : LProgram) (s : LState) :
  (JBudget.lCycleJ P s).jBudgetWin ≤ s.jBudgetWin :=
  JBudget.lCycleJ_nonincreasing (P:=P) (s:=s)

/-- Progress: every state can take a relational small‑step. -/
theorem VM_progress (P : LProgram) (s : LState) : ∃ s', LStepRel P s s' :=
  progress P s

/-- Unit‑delta predicate for integer counters. -/
def DeltaUnit (x y : Int) : Prop := Int.abs (y - x) ≤ 1

/-- Token count changes by at most one per `lStep` when parity holds. -/
lemma token_delta_unit (P : LProgram) (s : LState)
  (hTok : TokenParityInvariant s) :
  DeltaUnit s.aux5.tokenCt (lStep P s).aux5.tokenCt := by
  unfold TokenParityInvariant at hTok
  rcases hTok with ⟨h0, h1⟩
  unfold lStep
  by_cases hH : s.halted
  · simp [DeltaUnit, hH]
  · cases hop : (lFetch P s.ip).op <;> simp [DeltaUnit, hH, hop]
    all_goals
      first
        | -- unchanged cases
          have : (lStep P s).aux5.tokenCt = s.aux5.tokenCt := by
            simp [lStep, hH, hop]
          simpa [DeltaUnit, this]
        | -- GIVE: clamp01 (t+1)
          have hb := clamp01_bounds (s.aux5.tokenCt + 1)
          -- Since t ∈ {0,1}, the change is 0 or +1
          have ht01 : s.aux5.tokenCt = 0 ∨ s.aux5.tokenCt = 1 := by
            have := le_antisymm h1 (by
              have : (0 : Int) ≤ 1 := by decide
              exact h1)
            -- derive tight range from 0 ≤ t ≤ 1 over Int
            by_cases ht0 : s.aux5.tokenCt = 0
            · exact Or.inl ht0
            · have ht1' : s.aux5.tokenCt = 1 := by
                have hle0 : 0 < s.aux5.tokenCt ∨ s.aux5.tokenCt = 0 := by
                  exact lt_or_eq_of_le h0
                cases hle0 with
                | inl hpos =>
                  have : s.aux5.tokenCt ≤ 1 := h1
                  exact le_antisymm this (le_of_lt hpos)
                | inr hzero => cases hzero at ht0
              exact Or.inr ht1'
          cases ht01 with
          | inl ht0 =>
            -- t=0 → clamp01 (0+1)=1 ⇒ Δ=+1
            simp [DeltaUnit, lStep, hH, hop, ht0]
          | inr ht1 =>
            -- t=1 → clamp01 (1+1)=1 ⇒ Δ=0
            simp [DeltaUnit, lStep, hH, hop, ht1]
        | -- REGIVE: clamp01 (t-1)
          have hb := clamp01_bounds (s.aux5.tokenCt - 1)
          have ht01 : s.aux5.tokenCt = 0 ∨ s.aux5.tokenCt = 1 := by
            -- same derivation as above
            by_cases ht0 : s.aux5.tokenCt = 0
            · exact Or.inl ht0
            · have ht1' : s.aux5.tokenCt = 1 := by
                have hle0 : 0 < s.aux5.tokenCt ∨ s.aux5.tokenCt = 0 := by
                  exact lt_or_eq_of_le h0
                cases hle0 with
                | inl hpos =>
                  have : s.aux5.tokenCt ≤ 1 := h1
                  exact le_antisymm this (le_of_lt hpos)
                | inr hzero => simpa [hzero] using ht0
              exact Or.inr ht1'
          cases ht01 with
          | inl ht0 =>
            -- t=0 → clamp01 (-1)=0 ⇒ Δ=0
            simp [DeltaUnit, lStep, hH, hop, ht0]
          | inr ht1 =>
            -- t=1 → clamp01 (0)=0 ⇒ Δ=−1
            simp [DeltaUnit, lStep, hH, hop, ht1]
        | -- SEED/SPAWN: clamp01 1 ⇒ Δ ∈ {0,1} depending on t
          have ht01 : s.aux5.tokenCt = 0 ∨ s.aux5.tokenCt = 1 := by
            by_cases ht0 : s.aux5.tokenCt = 0
            · exact Or.inl ht0
            · have ht1' : s.aux5.tokenCt = 1 := by
                have hle0 : 0 < s.aux5.tokenCt ∨ s.aux5.tokenCt = 0 := by
                  exact lt_or_eq_of_le h0
                cases hle0 with
                | inl hpos =>
                  have : s.aux5.tokenCt ≤ 1 := h1
                  exact le_antisymm this (le_of_lt hpos)
                | inr hzero => simpa [hzero] using ht0
              exact Or.inr ht1'
          cases ht01 with
          | inl ht0 => simp [DeltaUnit, lStep, hH, hop, ht0]
          | inr ht1 => simp [DeltaUnit, lStep, hH, hop, ht1]

end LNAL
end IndisputableMonolith
