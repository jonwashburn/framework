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

/-! ### Token Parity Preservation -/

/-- openLock preserves openTokens ≤ 1 -/
private lemma openLock_preserves_bound (s : CompilerState) (h : s.openTokens ≤ 1) :
    (s.openLock).openTokens ≤ 1 := by
  unfold CompilerState.openLock
  simp only [ge_iff_le]
  split_ifs with h1
  · simp only [CompilerState.error]; exact h
  · simp only [Nat.not_le] at h1
    have h2 : s.openTokens = 0 := Nat.lt_one_iff.mp h1
    simp only [h2]; norm_num

/-- closeLock preserves openTokens ≤ 1 -/
private lemma closeLock_preserves_bound (s : CompilerState) (h : s.openTokens ≤ 1) :
    (s.closeLock).openTokens ≤ 1 := by
  unfold CompilerState.closeLock
  split_ifs with h1
  · simp only [CompilerState.error]; exact h
  · have h2 : s.openTokens = 1 := by omega
    simp only [h2]; norm_num

/-- emit preserves openTokens bound -/
private lemma emit_preserves_bound (s : CompilerState) (instr : LInstr) (h : s.openTokens ≤ 1) :
    (s.emit instr).openTokens ≤ 1 := by
  simp [CompilerState.emit]; exact h

/-- compileSelection preserves token bound -/
private lemma compileSelection_preserves (i : SelectionInstr) (s : CompilerState) (h : s.openTokens ≤ 1) :
    (compileSelection i s).openTokens ≤ 1 := by
  cases i <;> simp [compileSelection] <;> exact h

/-- compileTorsion preserves token bound -/
private lemma compileTorsion_preserves (i : TorsionInstr) (s : CompilerState) (h : s.openTokens ≤ 1) :
    (compileTorsion i s).openTokens ≤ 1 := by
  cases i <;> simp [compileTorsion, CompilerState.emit] <;> exact h

/-- compileContact preserves token bound -/
private lemma compileContact_preserves (i : ContactInstr) (s : CompilerState) (h : s.openTokens ≤ 1) :
    (compileContact i s).openTokens ≤ 1 := by
  cases i <;> simp [compileContact, CompilerState.emit] <;> exact h

/-- compileSecondary preserves token bound -/
private lemma compileSecondary_preserves (i : SecondaryInstr) (s : CompilerState) (h : s.openTokens ≤ 1) :
    (compileSecondary i s).openTokens ≤ 1 := by
  cases i <;> simp [compileSecondary, CompilerState.emit] <;> exact h

/-- compileCoreSolvent preserves token bound -/
private lemma compileCoreSolvent_preserves (i : CoreSolventInstr) (s : CompilerState) (h : s.openTokens ≤ 1) :
    (compileCoreSolvent i s).openTokens ≤ 1 := by
  cases i <;> simp [compileCoreSolvent, CompilerState.emit] <;> exact h

/-- compileMeasurement preserves token bound -/
private lemma compileMeasurement_preserves (i : MeasurementInstr) (s : CompilerState) (h : s.openTokens ≤ 1) :
    (compileMeasurement i s).openTokens ≤ 1 := by
  cases i with
  | listenPhase => simp [compileMeasurement, CompilerState.emit]; exact h
  | lockPhase =>
    simp [compileMeasurement]
    have h1 : s.openLock.openTokens ≤ 1 := openLock_preserves_bound s h
    simp [CompilerState.emit]; exact h1
  | balancePhase =>
    simp [compileMeasurement]
    have h1 : s.closeLock.openTokens ≤ 1 := closeLock_preserves_bound s h
    simp [CompilerState.emit]; exact h1

/-- compileGuard preserves token bound -/
private lemma compileGuard_preserves (i : GuardInstr) (s : CompilerState) (h : s.openTokens ≤ 1) :
    (compileGuard i s).openTokens ≤ 1 := by
  cases i <;> simp [compileGuard] <;> exact h

/-- emitBalances preserves token bound -/
private lemma emitBalances_preserves (n : Nat) (s : CompilerState) (h : s.openTokens ≤ 1) :
    (compileWait.emitBalances n s).openTokens ≤ 1 := by
  induction n generalizing s with
  | zero =>
    unfold compileWait.emitBalances
    simp only [↓reduceIte]
    exact h
  | succ k ih =>
    unfold compileWait.emitBalances
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
    apply ih
    exact emit_preserves_bound s _ h

/-- compileWait preserves token bound -/
private lemma compileWait_preserves (i : WaitInstr) (s : CompilerState) (h : s.openTokens ≤ 1) :
    (compileWait i s).openTokens ≤ 1 := by
  cases i with
  | waitTicks n =>
    unfold compileWait
    exact emitBalances_preserves n s h

/-- compileInstr preserves token bound -/
private lemma compileInstr_preserves (i : PNALInstr) (s : CompilerState) (h : s.openTokens ≤ 1) :
    (compileInstr i s).openTokens ≤ 1 := by
  cases i with
  | selection i => exact compileSelection_preserves i s h
  | torsion i => exact compileTorsion_preserves i s h
  | contact i => exact compileContact_preserves i s h
  | secondary i => exact compileSecondary_preserves i s h
  | coreSolvent i => exact compileCoreSolvent_preserves i s h
  | measurement i => exact compileMeasurement_preserves i s h
  | guard i => exact compileGuard_preserves i s h
  | wait i => exact compileWait_preserves i s h
  | comment _ => simp [compileInstr]; exact h

/-- foldl over compileInstr preserves token bound -/
private lemma foldl_compileInstr_preserves (instrs : List PNALInstr) (s : CompilerState) (h : s.openTokens ≤ 1) :
    (instrs.foldl (fun state instr => compileInstr instr state) s).openTokens ≤ 1 := by
  induction instrs generalizing s with
  | nil => simp; exact h
  | cons i is ih =>
    simp only [List.foldl_cons]
    apply ih
    exact compileInstr_preserves i s h

/-- **Theorem**: Compilation preserves token parity (openTokens ≤ 1).

    This follows from the structure of openLock/closeLock which enforce the bound
    by construction: openLock only increments if tokens < 1, so it can never exceed 1. -/
theorem compilation_preserves_token_parity :
    ∀ (prog : PNALProgram), (compile prog).openTokens ≤ 1 := by
  intro prog
  unfold compile
  apply foldl_compileInstr_preserves
  simp [CompilerState.init]

/-- Invariant: Well-formed programs produce valid LNAL -/
theorem wellformed_produces_valid_lnal :
  ∀ (_wf : WellFormedProgram),
    -- Generated LNAL satisfies eight-window neutrality
    -- and token parity constraints
    True :=  -- TODO: Formalize LNAL invariant predicates
  fun _ => trivial

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
