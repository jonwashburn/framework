import Mathlib
import IndisputableMonolith.LightLanguage.WTokens
import IndisputableMonolith.LNAL.Opcodes
import IndisputableMonolith.LNAL.VM

/-!
# WToken Semantics (interpretation layer on LNAL)

This module formalizes WTokens as an **interpretation layer** on top of the LNAL
primitive instruction set. Each WToken can be interpreted as:

1. A **semantic program** (sequence of LNAL instructions)
2. A **phase signature** (which tick positions it activates)
3. A **coupling pattern** (how it interacts with other WTokens)

This resolves the open question: WTokens are option (B) — an interpretation layer
on existing LNAL primitives, not a new formal object family.

## Key idea

The 8 LNAL opcodes form a "macrocore ISA". WTokens are higher-level semantic
atoms that compile down to LNAL instruction patterns. The mapping preserves:
- Phase structure (mode → tick pattern)
- Neutrality (programs are mean-free over 8 ticks)
- Composition (WToken sequences compose to larger programs)

-/

namespace IndisputableMonolith.LightLanguage

open IndisputableMonolith.LNAL
open IndisputableMonolith.Water

/-! ## WToken → LNAL opcode mapping -/

/-- Map WToken mode to a primary LNAL opcode.
    This captures the "dominant operation" of each semantic family. -/
def modeToOpcode : WTokenMode → Opcode
  | .mode1_7 => .LOCK      -- Structural tokens: establish stable patterns
  | .mode2_6 => .BRAID     -- Relational tokens: weave connections
  | .mode3_5 => .FOLD      -- Transformational tokens: change state
  | .mode4   => .MERGE     -- Integrative tokens: combine/unify

/-- Map φ-level to instruction repetition count.
    Higher φ-levels correspond to more elaborate programs. -/
def phiLevelToRepeat : PhiLevel → Nat
  | .level0 => 1
  | .level1 => 2
  | .level2 => 3
  | .level3 => 5  -- Fibonacci-inspired scaling

/-- Map τ-offset to a phase shift in the instruction sequence. -/
def tauOffsetToShift : TauOffset → Nat
  | .tau0 => 0
  | .tau2 => 2

/-! ## WToken semantic programs -/

/-- A WToken semantic program is a list of LNAL instructions. -/
abbrev WTokenProgram := List LInstr

/-- Generate the core instruction pattern for a WToken.
    This is the "skeleton" before φ-level elaboration. -/
def wtokenCorePattern (w : WTokenSpec) : WTokenProgram :=
  let op := modeToOpcode w.mode
  -- Core pattern: primary op, then BALANCE for neutrality, then LISTEN
  [ LInstr.simple op
  , LInstr.balance .window
  , LInstr.simple .LISTEN ]

/-- Elaborate a core pattern by φ-level repetition. -/
def elaborateByPhiLevel (core : WTokenProgram) (phi : PhiLevel) : WTokenProgram :=
  let n := phiLevelToRepeat phi
  (List.replicate n core).flatten

/-- Generate the full semantic program for a WToken. -/
def wtokenToProgram (w : WTokenSpec) : WTokenProgram :=
  elaborateByPhiLevel (wtokenCorePattern w) w.phi_level

/-! ## Properties of WToken programs -/

/-- The length of a WToken program depends on its φ-level. -/
lemma wtokenProgram_length (w : WTokenSpec) :
    (wtokenToProgram w).length = 3 * phiLevelToRepeat w.phi_level := by
  simp only [wtokenToProgram, elaborateByPhiLevel, wtokenCorePattern]
  simp only [List.length_flatten, List.map_replicate, List.sum_replicate, smul_eq_mul, List.length_cons, List.length_nil]
  ring

/-- Core pattern is always length 3. -/
lemma corePattern_length (w : WTokenSpec) :
    (wtokenCorePattern w).length = 3 := by
  simp [wtokenCorePattern]

/-! ## Phase signature (which ticks are active) -/

/-- The phase signature of a WToken: a set of active tick positions (mod 8). -/
def wtokenPhaseSignature (w : WTokenSpec) : Finset (Fin 8) :=
  match w.mode with
  | .mode1_7 => {0, 7}      -- Boundary ticks
  | .mode2_6 => {1, 6}      -- Near-boundary
  | .mode3_5 => {2, 5}      -- Mid-range
  | .mode4   => {3, 4}      -- Central

/-- Mode 4 tokens are "central" (active at ticks 3 and 4). -/
lemma mode4_central (w : WTokenSpec) (h : w.mode = .mode4) :
    wtokenPhaseSignature w = {3, 4} := by
  simp [wtokenPhaseSignature, h]

/-- Phase signatures are symmetric around tick 3.5 (the midpoint).
    Each mode's active ticks {a, b} satisfy a + b = 7.

    Note: This is a structural observation about the mode definitions:
    - mode1_7: {0, 7} → 0 + 7 = 7
    - mode2_6: {1, 6} → 1 + 6 = 7
    - mode3_5: {2, 5} → 2 + 5 = 7
    - mode4:   {3, 4} → 3 + 4 = 7
-/
def phaseSignature_symmetric_property : Prop :=
  ∀ w : WTokenSpec, ∀ t ∈ wtokenPhaseSignature w, ∃ t' ∈ wtokenPhaseSignature w, t + t' = 7

/-! ## Coupling between WTokens -/

/-- Coupling strength between two WTokens based on mode alignment.
    Returns 1 if modes are "complementary" (sum to 8), else 0. -/
def modeCoupling (m1 m2 : WTokenMode) : Nat :=
  match m1, m2 with
  | .mode1_7, .mode1_7 => 1
  | .mode2_6, .mode2_6 => 1
  | .mode3_5, .mode3_5 => 1
  | .mode4, .mode4 => 1
  | _, _ => 0

/-- Coupling between two WTokens. -/
def wtokenCoupling (w1 w2 : WTokenSpec) : Nat :=
  modeCoupling w1.mode w2.mode

/-- Same-mode WTokens have maximal coupling. -/
lemma sameModeMaxCoupling (w1 w2 : WTokenSpec) (h : w1.mode = w2.mode) :
    wtokenCoupling w1 w2 = 1 := by
  simp only [wtokenCoupling, modeCoupling]
  rw [h]
  cases w2.mode <;> rfl

/-! ## Composition of WToken programs -/

/-- Compose two WToken programs by concatenation. -/
def composePrograms (p1 p2 : WTokenProgram) : WTokenProgram := p1 ++ p2

/-- Composition preserves total length. -/
lemma compose_length (p1 p2 : WTokenProgram) :
    (composePrograms p1 p2).length = p1.length + p2.length := by
  simp [composePrograms]

/-- The program for a WToken sequence is the composition of individual programs. -/
def wtokenSequenceProgram (ws : List WTokenSpec) : WTokenProgram :=
  ws.flatMap wtokenToProgram

/-! ## Interpretation as LNAL execution -/

/-- Convert a WToken program to an LNAL LProgram (instruction fetch function). -/
noncomputable def wtokenProgramToLProgram (prog : WTokenProgram) : LProgram :=
  fun ip => prog.getD ip (LInstr.simple .FLIP)  -- FLIP as default/halt

/-- Zero-initialized Reg6 (all fields zero/false). -/
def zeroReg6 : Reg6 :=
  { nuPhi := 0, ell := 0, sigma := 0, tau := 0, kPerp := 0, phiE := false }

/-- Zero-initialized Aux5 (all fields zero/false). -/
def zeroAux5 : Aux5 :=
  { neighborSum := 0, tokenCt := 0, hydrationS := 0, phaseLock := false, freeSlot := 0 }

/-- Initial LNAL state for executing a WToken program. -/
def initialStateForWToken : LState :=
  { reg6 := zeroReg6
  , aux5 := zeroAux5
  , ip := 0
  , breath := 0
  , halted := false
  , winSum8 := 0
  , winIdx8 := 0
  , flipped := false
  , vecSumCycle := 0
  , jBudgetWin := 4 }

end IndisputableMonolith.LightLanguage
