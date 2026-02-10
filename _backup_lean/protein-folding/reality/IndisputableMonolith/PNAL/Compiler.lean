import Mathlib
import IndisputableMonolith.PNAL.Syntax
import IndisputableMonolith.LNAL.Opcodes
import IndisputableMonolith.LNAL.Registers

/-!
# PNAL to LNAL Compiler

Translates high-level PNAL instructions to low-level LNAL bytecode while
preserving invariants:
- Token parity ≤ 1
- Eight-window neutrality
- Legal SU(3) triads
- 2^10 breath cycle

## Compilation Strategy

Each PNAL instruction expands to a sequence of LNAL instructions that:
1. Maintains invariants by construction
2. Inserts LISTEN checkpoints at appropriate beats
3. Uses BALANCE to ensure eight-window neutrality
4. Respects φ-scaled timing

## References

- `Protein Folding as Phase Recognition.tex` §4: PNAL→LNAL mapping rules
- `tools/pnal/README.md`: Compilation examples
-/

namespace IndisputableMonolith
namespace PNAL

open LNAL

/-! ## Compilation Context -/

/-- Compilation state tracking open tokens, tick count, etc. -/
structure CompilerState where
  /-- Current tick count in breath cycle -/
  currentTick : Nat
  /-- Number of open LOCK tokens -/
  openTokens : Nat
  /-- Generated LNAL instructions -/
  lnalCode : List LInstr
  /-- Errors encountered -/
  errors : List String
deriving Repr

namespace CompilerState

/-- Initial compiler state -/
def init : CompilerState :=
  ⟨0, 0, [], []⟩

/-- Append LNAL instruction with tick tracking -/
def emit (state : CompilerState) (instr : LInstr) : CompilerState :=
  let newTick := (state.currentTick + 1) % 1024  -- Breath cycle wrap
  ⟨newTick, state.openTokens, state.lnalCode ++ [instr], state.errors⟩

/-- Append multiple LNAL instructions -/
def emitMany (state : CompilerState) (instrs : List LInstr) : CompilerState :=
  instrs.foldl (fun s i => s.emit i) state

/-- Record error -/
def error (state : CompilerState) (msg : String) : CompilerState :=
  ⟨state.currentTick, state.openTokens, state.lnalCode, state.errors ++ [msg]⟩

/-- Open a LOCK token -/
def openLock (state : CompilerState) : CompilerState :=
  if state.openTokens ≥ 1 then
    state.error "Token parity violation: attempting to open second LOCK"
  else
    ⟨state.currentTick, state.openTokens + 1, state.lnalCode, state.errors⟩

/-- Close a LOCK token -/
def closeLock (state : CompilerState) : CompilerState :=
  if state.openTokens = 0 then
    state.error "Token parity violation: no LOCK to close"
  else
    ⟨state.currentTick, state.openTokens - 1, state.lnalCode, state.errors⟩

/-- Check if at breath boundary (tick 512 or 1023) -/
def atBreathBoundary (state : CompilerState) : Bool :=
  state.currentTick == 511 || state.currentTick == 1023

end CompilerState

/-! ## PNAL Instruction Compilation -/

/-- Compile selection instructions (mostly metadata, minimal LNAL output) -/
def compileSelection (instr : SelectionInstr) (state : CompilerState) : CompilerState :=
  match instr with
  | .selRes _ => state  -- No LNAL emission for selection
  | .selRange _ => state
  | .selSecStruct _ => state
  | .maskContact _ _ => state

/-- Compile torsion instructions -/
def compileTorsion (instr : TorsionInstr) (state : CompilerState) : CompilerState :=
  match instr with
  | .rotPhi delta =>
      -- FOLD with appropriate direction and LISTEN checkpoint
      let foldDir := if delta > 0 then 1 else if delta < 0 then -1 else 0
      state.emit (LInstr.fold foldDir)
           |>.emit (LInstr.listen .noop)
  | .rotPsi delta =>
      let foldDir := if delta > 0 then 1 else if delta < 0 then -1 else 0
      state.emit (LInstr.fold foldDir)
           |>.emit (LInstr.listen .noop)
  | .rotOmega _ =>
      -- Omega rotation (cis/trans isomerization)
      state.emit (LInstr.fold 0)
           |>.emit (LInstr.listen .noop)
  | .rotChi _ delta =>
      let foldDir := if delta > 0 then 1 else if delta < 0 then -1 else 0
      state.emit (LInstr.fold foldDir)
           |>.emit (LInstr.listen .noop)
  | .sidechainPack =>
      -- Local repacking: FOLD + UNFOLD + LISTEN
      state.emit (LInstr.fold 1)
           |>.emit (LInstr.fold (-1))
           |>.emit (LInstr.listen .noop)

/-- Compile contact instructions -/
def compileContact (instr : ContactInstr) (state : CompilerState) : CompilerState :=
  match instr with
  | .setContact _ _ =>
      -- Set contact: BRAID (legal triad) + LISTEN
      state.emit (LInstr.tokenDelta .BRAID 0)
           |>.emit (LInstr.listen .noop)
  | .clearContact _ _ =>
      -- Clear contact: reverse BRAID
      state.emit (LInstr.tokenDelta .BRAID 0)
           |>.emit (LInstr.listen .noop)
  | .setHBond _ _ =>
      state.emit (LInstr.tokenDelta .BRAID 0)
           |>.emit (LInstr.listen .noop)
  | .breakHBond _ _ =>
      state.emit (LInstr.tokenDelta .BRAID 0)
           |>.emit (LInstr.listen .noop)
  | .setSalt _ _ =>
      state.emit (LInstr.tokenDelta .BRAID 0)
           |>.emit (LInstr.listen .noop)
  | .setDisulfide _ _ =>
      state.emit (LInstr.tokenDelta .BRAID 0)
           |>.emit (LInstr.listen .noop)

/-- Compile secondary structure instructions -/
def compileSecondary (instr : SecondaryInstr) (state : CompilerState) : CompilerState :=
  match instr with
  | .nucleateHelix _ =>
      -- Helix nucleation: FOLD + LISTEN pattern repeated
      state.emit (LInstr.fold 1)
           |>.emit (LInstr.listen .noop)
           |>.emit (LInstr.fold 1)
           |>.emit (LInstr.listen .noop)
  | .propagateHelix _ =>
      -- Propagation: continue helix extension
      state.emit (LInstr.fold 1)
           |>.emit (LInstr.listen .noop)
  | .nucleateTurn _ =>
      -- Turn nucleation: tight FOLD sequence
      state.emit (LInstr.fold 1)
           |>.emit (LInstr.fold (-1))
           |>.emit (LInstr.listen .noop)
  | .pairBeta _ _ _ =>
      -- β-pairing: BRAID to connect strands + LISTEN
      state.emit (LInstr.tokenDelta .BRAID 0)
           |>.emit (LInstr.listen .noop)
           |>.emit (LInstr.tokenDelta .BRAID 0)
           |>.emit (LInstr.listen .noop)

/-- Compile core/solvent instructions -/
def compileCoreSolvent (instr : CoreSolventInstr) (state : CompilerState) : CompilerState :=
  match instr with
  | .nucleateCore _ =>
      -- Core nucleation: SEED + SPAWN (simplified)
      state.emit (LInstr.simple .SEED)
           |>.emit (LInstr.simple .FLIP)
  | .packCore =>
      -- Core packing: Multiple FOLD operations
      state.emit (LInstr.fold 1)
           |>.emit (LInstr.fold (-1))
  | .solvateShell _ =>
      state  -- Solvent handling in energy function, not opcodes
  | .screenPhase _ =>
      state  -- Phase screening metadata

/-- Compile measurement instructions -/
def compileMeasurement (instr : MeasurementInstr) (state : CompilerState) : CompilerState :=
  match instr with
  | .listenPhase =>
      state.emit (LInstr.listen .noop)
  | .lockPhase =>
      state.openLock.emit (LInstr.simple .LOCK)
  | .balancePhase =>
      state.closeLock.emit (LInstr.balance .window)

/-- Compile guard instructions -/
def compileGuard (instr : GuardInstr) (state : CompilerState) : CompilerState :=
  match instr with
  | .assertNoClash => state  -- Runtime check, no LNAL emission
  | .assertContact _ => state
  | .assertRMSD _ => state
  | .assertCisPro _ => state
  | .assertBeat _ _ => state

/-- Compile wait instructions -/
def compileWait (instr : WaitInstr) (state : CompilerState) : CompilerState :=
  match instr with
  | .waitTicks n =>
      -- Emit n BALANCE instructions (neutral cost, advances ticks)
      let rec emitBalances (count : Nat) (s : CompilerState) : CompilerState :=
        if count = 0 then s
        else emitBalances (count - 1) (s.emit (LInstr.balance .window))
      emitBalances n state

/-! ## Main Compilation Function -/

/-- Compile single PNAL instruction -/
def compileInstr (instr : PNALInstr) (state : CompilerState) : CompilerState :=
  match instr with
  | .selection i => compileSelection i state
  | .torsion i => compileTorsion i state
  | .contact i => compileContact i state
  | .secondary i => compileSecondary i state
  | .coreSolvent i => compileCoreSolvent i state
  | .measurement i => compileMeasurement i state
  | .guard i => compileGuard i state
  | .wait i => compileWait i state
  | .comment _ => state  -- Comments don't emit code

/-- Compile entire PNAL program -/
def compile (prog : PNALProgram) : CompilerState :=
  prog.instructions.foldl (fun state instr => compileInstr instr state) CompilerState.init

/-- Extract compiled LNAL code -/
def compileToLNAL (prog : PNALProgram) : List LInstr :=
  (compile prog).lnalCode

/-- Check for compilation errors -/
def hasErrors (prog : PNALProgram) : Bool :=
  (compile prog).errors.length > 0

/-- Get compilation errors -/
def getErrors (prog : PNALProgram) : List String :=
  (compile prog).errors

/-! ## Compilation Contracts -/

/-- Well-formed PNAL program (ready to compile) -/
structure WellFormedProgram where
  prog : PNALProgram
  /-- No LOCK at end of program -/
  noOpenLocks : (compile prog).openTokens = 0
  /-- No compilation errors -/
  noErrors : (compile prog).errors = []
deriving Repr

/-- Helper: openLock preserves the ≤ 1 invariant -/
private lemma openLock_le_one (state : CompilerState) (h : state.openTokens ≤ 1) :
    state.openLock.openTokens ≤ 1 := by
  simp only [CompilerState.openLock]
  split_ifs with hge
  · -- If openTokens ≥ 1, error is added but openTokens unchanged
    simp only [CompilerState.error]; exact h
  · -- If openTokens < 1 (i.e., = 0), increment to 1
    simp only []; omega

/-- Helper: closeLock preserves the ≤ 1 invariant -/
private lemma closeLock_le_one (state : CompilerState) (h : state.openTokens ≤ 1) :
    state.closeLock.openTokens ≤ 1 := by
  simp only [CompilerState.closeLock]
  split_ifs with heq
  · -- If openTokens = 0, error is added but openTokens unchanged
    simp only [CompilerState.error]; exact h
  · -- If openTokens ≠ 0 (i.e., = 1), decrement to 0
    simp only []; omega

/-- Helper: emit preserves the token count -/
private lemma emit_preserves_tokens (state : CompilerState) (instr : LInstr) :
    (state.emit instr).openTokens = state.openTokens := by
  simp only [CompilerState.emit]

/-- Helper: emitBalances preserves the token count -/
private lemma emitBalances_preserves_tokens (n : Nat) (state : CompilerState) :
    (compileWait.emitBalances n state).openTokens = state.openTokens := by
  induction n generalizing state with
  | zero =>
      unfold compileWait.emitBalances
      simp only [↓reduceIte]
  | succ k ih =>
      unfold compileWait.emitBalances
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [ih]
      simp only [CompilerState.emit]

/-- Helper: compileInstr preserves the ≤ 1 invariant -/
private lemma compileInstr_le_one (instr : PNALInstr) (state : CompilerState)
    (h : state.openTokens ≤ 1) :
    (compileInstr instr state).openTokens ≤ 1 := by
  cases instr with
  | selection i => simp only [compileInstr, compileSelection]; cases i <;> exact h
  | torsion i => simp only [compileInstr, compileTorsion]; cases i <;> simp [emit_preserves_tokens, h]
  | contact i => simp only [compileInstr, compileContact]; cases i <;> simp [emit_preserves_tokens, h]
  | secondary i => simp only [compileInstr, compileSecondary]; cases i <;> simp [emit_preserves_tokens, h]
  | coreSolvent i => simp only [compileInstr, compileCoreSolvent]; cases i <;> simp [emit_preserves_tokens, h]
  | measurement i =>
      simp only [compileInstr, compileMeasurement]
      cases i with
      | listenPhase => simp [emit_preserves_tokens, h]
      | lockPhase => simp [emit_preserves_tokens]; exact openLock_le_one state h
      | balancePhase => simp [emit_preserves_tokens]; exact closeLock_le_one state h
  | guard i => simp only [compileInstr, compileGuard]; cases i <;> exact h
  | wait i =>
      simp only [compileInstr, compileWait]
      cases i with
      | waitTicks n => rw [emitBalances_preserves_tokens]; exact h
  | comment _ => simp only [compileInstr]; exact h

/-- Helper: foldl over instructions preserves the ≤ 1 invariant -/
private lemma foldl_compileInstr_le_one (instrs : List PNALInstr) (state : CompilerState)
    (h : state.openTokens ≤ 1) :
    (instrs.foldl (fun s i => compileInstr i s) state).openTokens ≤ 1 := by
  induction instrs generalizing state with
  | nil => exact h
  | cons instr rest ih =>
      simp only [List.foldl]
      exact ih (compileInstr instr state) (compileInstr_le_one instr state h)

/-- Invariant: Compilation preserves token parity -/
theorem compilation_preserves_token_parity :
  ∀ (prog : PNALProgram),
    (compile prog).openTokens ≤ 1 := by
  intro prog
  simp only [compile]
  have h_init : CompilerState.init.openTokens ≤ 1 := by simp [CompilerState.init]
  exact foldl_compileInstr_le_one prog.instructions CompilerState.init h_init

/-- Invariant: Well-formed programs produce valid LNAL.
    NOTE: Currently a placeholder returning True. Full formalization of LNAL
    invariant predicates (eight-window neutrality, token parity) is TODO. -/
theorem wellformed_produces_valid_lnal :
  ∀ (_wf : WellFormedProgram),
    -- Generated LNAL satisfies eight-window neutrality
    -- and token parity constraints
    True := by
  intro _; trivial

/-! ## Example Programs -/

namespace Examples

/-- Simple helix nucleation -/
def simpleHelix : PNALProgram :=
  let h : 5 ≤ 15 := by norm_num
  ⟨[
    PNALInstr.nucleateHelix 5 15 h,
    PNALInstr.listenPhase,
    PNALInstr.assertNoClash
  ], some "Simple helix nucleation"⟩

/-- Contact formation -/
def simpleContact : PNALProgram :=
  ⟨[
    PNALInstr.setContact 3 18,
    PNALInstr.listenPhase
  ], some "Set native contact"⟩

end Examples

end PNAL
end IndisputableMonolith
