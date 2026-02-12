import IndisputableMonolith.PNAL
open IndisputableMonolith

/-!
# PNAL Compiler Tests

Test suite for PNAL → LNAL compilation, verifying:
- Correct code generation
- Token parity preservation
- Error detection
- Invariant maintenance

## Test Categories

1. **Basic Compilation**: Simple programs compile without errors
2. **Token Parity**: LOCK/BALANCE pairs balanced
3. **Error Detection**: Invalid programs caught
4. **Code Generation**: Output matches expected LNAL sequences

-/

namespace IndisputableMonolith
namespace PNAL
namespace Tests

open PNAL

/-! ## Basic Compilation Tests -/

/-- Test: Simple helix compiles -/
theorem test_simpleHelix_compiles : ¬hasErrors Examples.simpleHelix := by
  unfold hasErrors compile
  simp [Examples.simpleHelix, CompilerState.init, compileInstr,
    PNALInstr.nucleateHelix, compileSecondary,
    PNALInstr.listenPhase, compileMeasurement,
    PNALInstr.assertNoClash, compileGuard,
    CompilerState.emit]

example : ¬hasErrors Examples.simpleHelix := test_simpleHelix_compiles

/-- Test: Simple contact compiles without errors. -/
theorem test_simpleContact_compiles : ¬hasErrors Examples.simpleContact := by
  unfold hasErrors compile
  simp [Examples.simpleContact, CompilerState.init, compileInstr,
    PNALInstr.setContact, compileContact,
    PNALInstr.listenPhase, compileMeasurement,
    CompilerState.emit]

example : ¬hasErrors Examples.simpleContact := test_simpleContact_compiles

/-! ## Token Parity Tests -/

/-- Test: Empty program has zero open tokens -/
example : (compile PNALProgram.empty).openTokens = 0 := by
  unfold compile PNALProgram.empty CompilerState.init
  simp [List.foldl]

/-- Test: LISTEN doesn't affect token count -/
example :
    let prog : PNALProgram := ⟨[.measurement .listenPhase], none⟩
    (compile prog).openTokens = 0 := by
  unfold compile CompilerState.init
  simp [List.foldl, compileInstr, compileMeasurement]
  unfold CompilerState.emit
  simp

/-- Test: Balanced LOCK/BALANCE has zero final tokens. -/
theorem test_lock_balance_tokens :
    let prog : PNALProgram := ⟨[
      .measurement .lockPhase,
      .measurement .listenPhase,
      .measurement .balancePhase
    ], none⟩
    (compile prog).openTokens = 0 := by
  unfold compile CompilerState.init
  simp only [List.foldl, compileInstr, compileMeasurement]
  unfold CompilerState.openLock CompilerState.closeLock CompilerState.emit
  -- After LOCK: openTokens = 1
  -- After LISTEN: openTokens = 1 (unchanged)
  -- After BALANCE with openTokens = 1: openTokens = 0
  norm_num

example :
    let prog : PNALProgram := ⟨[
      .measurement .lockPhase,
      .measurement .listenPhase,
      .measurement .balancePhase
    ], none⟩
    (compile prog).openTokens = 0 := test_lock_balance_tokens

/-! ## Code Generation Tests -/

/-- Test: Single rotPhi generates FOLD + LISTEN (2 LNAL instructions). -/
theorem test_rotPhi_generates_two :
    let prog : PNALProgram := ⟨[.torsion (.rotPhi 1)], none⟩
    let lnal := compileToLNAL prog
    lnal.length = 2 := by
  unfold compileToLNAL compile CompilerState.init
  simp [List.foldl, compileInstr, compileTorsion, CompilerState.emit]

example :
    let prog : PNALProgram := ⟨[.torsion (.rotPhi 1)], none⟩
    let lnal := compileToLNAL prog
    lnal.length = 2 := test_rotPhi_generates_two

/-- Test: rotPhi positive delta generates code -/
theorem test_rotPhi_positive :
    let prog : PNALProgram := ⟨[.torsion (.rotPhi 5)], none⟩
    let lnal := compileToLNAL prog
    lnal.length ≥ 2 := by
  unfold compileToLNAL compile CompilerState.init
  have hlen :
      (List.foldl (fun state instr => compileInstr instr state) ⟨0, 0, [], []⟩
          [.torsion (.rotPhi 5)]).lnalCode.length = 2 := by
    simp [List.foldl, compileInstr, compileTorsion, CompilerState.emit]
  simpa [hlen]

/-! ## Error Detection Tests -/

/-- Test: Token parity violation detected (double LOCK triggers error). -/
theorem test_double_lock_error :
    let prog : PNALProgram := ⟨[
      .measurement .lockPhase,
      .measurement .lockPhase  -- Second LOCK without BALANCE
    ], none⟩
    hasErrors prog := by
  unfold hasErrors compile CompilerState.init
  simp only [List.foldl, compileInstr, compileMeasurement]
  unfold CompilerState.openLock CompilerState.error CompilerState.emit
  -- After first LOCK: openTokens = 1, errors = []
  -- Second LOCK: openTokens ≥ 1, so error is added
  -- Final errors.length = 1 > 0
  simp only []
  decide

example :
    let prog : PNALProgram := ⟨[
      .measurement .lockPhase,
      .measurement .lockPhase  -- Second LOCK without BALANCE
    ], none⟩
    hasErrors prog := test_double_lock_error

/-! ## Invariant Tests -/

/-- Test: Compilation preserves token parity for any program -/
theorem test_token_parity_preserved (prog : PNALProgram) :
    (compile prog).openTokens ≤ 1 :=
  compilation_preserves_token_parity prog

/-! ## Integration Tests -/

/-- Test: Realistic folding program compiles -/
def realisticProtein : PNALProgram :=
  let h1 : 5 ≤ 15 := by norm_num
  let h2 : 20 ≤ 30 := by norm_num
  ⟨[
    -- Nucleate first helix
    .secondary (.nucleateHelix ⟨5, 15, h1⟩),
    .measurement .listenPhase,

    -- Nucleate second helix
    .secondary (.nucleateHelix ⟨20, 30, h2⟩),
    .measurement .listenPhase,

    -- Form contact between helices
    .contact (.setContact 10 25),
    .measurement .listenPhase,

    -- Pack core
    .coreSolvent .packCore,
    .measurement .listenPhase,

    -- Final check
    .guard .assertNoClash
  ], some "Two-helix bundle"⟩

/-- Test: Realistic protein program compiles without errors. -/
theorem test_realisticProtein_compiles : ¬hasErrors realisticProtein := by
  unfold hasErrors compile realisticProtein
  simp [realisticProtein, CompilerState.init, List.foldl, compileInstr,
    compileSecondary, compileMeasurement, compileContact,
    compileCoreSolvent, compileGuard, CompilerState.emit]

example : ¬hasErrors realisticProtein := test_realisticProtein_compiles

/-- Test: Realistic program generates non-empty LNAL output. -/
theorem test_realisticProtein_nonempty :
    (compileToLNAL realisticProtein).length > 0 := by
  unfold compileToLNAL compile realisticProtein
  simp [realisticProtein, CompilerState.init, List.foldl, compileInstr,
    compileSecondary, compileMeasurement, compileContact,
    compileCoreSolvent, compileGuard, CompilerState.emit]

example : (compileToLNAL realisticProtein).length > 0 := test_realisticProtein_nonempty

/-! ## Regression Tests -/

/-- Test: Compilation is deterministic -/
theorem compilation_deterministic (prog : PNALProgram) :
    compile prog = compile prog := by
  rfl

/-- Test: Empty program compiles to empty code -/
example : compileToLNAL PNALProgram.empty = [] := by
  unfold compileToLNAL compile PNALProgram.empty CompilerState.init
  simp [List.foldl]

end Tests
end PNAL
end IndisputableMonolith
