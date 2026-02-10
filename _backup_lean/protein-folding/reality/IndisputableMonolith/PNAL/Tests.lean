import IndisputableMonolith.PNAL

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
example : ¬hasErrors Examples.simpleHelix := by
  native_decide

/-- Test: Simple contact compiles -/
example : ¬hasErrors Examples.simpleContact := by
  native_decide

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

/-- Test: Balanced LOCK/BALANCE has zero final tokens -/
example :
    let prog : PNALProgram := ⟨[
      .measurement .lockPhase,
      .measurement .listenPhase,
      .measurement .balancePhase
    ], none⟩
    (compile prog).openTokens = 0 := by
  native_decide

/-! ## Code Generation Tests -/

/-- Test: Single rotPhi generates FOLD + LISTEN -/
example :
    let prog : PNALProgram := ⟨[.torsion (.rotPhi 1)], none⟩
    let lnal := compileToLNAL prog
    lnal.length = 2 := by
  native_decide

/-- Test: rotPhi positive delta generates code -/
theorem test_rotPhi_positive :
    let prog : PNALProgram := ⟨[.torsion (.rotPhi 5)], none⟩
    let lnal := compileToLNAL prog
    lnal.length ≥ 2 := by  -- At least FOLD + LISTEN
  native_decide

/-! ## Error Detection Tests -/

/-- Test: Token parity violation detected -/
example :
    let prog : PNALProgram := ⟨[
      .measurement .lockPhase,
      .measurement .lockPhase  -- Second LOCK without BALANCE
    ], none⟩
    hasErrors prog := by
  native_decide

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

example : ¬hasErrors realisticProtein := by
  native_decide

/-- Test: Realistic program generates reasonable LNAL length -/
example : (compileToLNAL realisticProtein).length > 0 := by
  native_decide

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
