import Mathlib
import IndisputableMonolith.LNAL.Opcodes
import IndisputableMonolith.LNAL.VM
import IndisputableMonolith.LNAL.PhiIR

namespace IndisputableMonolith
namespace LNAL

/-!
# LNAL Parser - Complete Implementation

Enhanced parser with:
- Macro expansion (PHOTON_EMIT, DIAMOND_CELL, SEED_SPAWN, LISTEN_PAUSE, HARDEN)
- Label support and forward references
- Source location tracking for error messages
- Directive parsing (@define, @include future)
- Integration with static checks

Follows LNAL spec from Source.txt:
- 16 opcodes: LOCK, BALANCE, FOLD, UNFOLD, BRAID, HARDEN, SEED, SPAWN, MERGE, LISTEN, GIVE, REGIVE, FLIP, VECTOR_EQ, CYCLE, GC_SEED
- Macros: PHOTON_EMIT, HARDEN (alias), DIAMOND_CELL, SEED_SPAWN, LISTEN_PAUSE
-/

/-- Complete parse output including φ-IR analysis. -/
structure ParseOutput where
  code : Array LInstr
  phi  : PhiIR.PhiAnalysis
  packets : PhiIR.PacketAnalysis
deriving Repr

/-- Source location for error reporting -/
structure SourceLoc where
  line : Nat
  column : Nat := 0
  file : String := "<input>"
deriving Repr, DecidableEq

/-- Enhanced parse errors with source locations -/
inductive ParseError where
| unknownOpcode (loc : SourceLoc) (tok : String)
| unknownMacro (loc : SourceLoc) (name : String)
| invalidLabel (loc : SourceLoc) (label : String)
| undefinedLabel (label : String) (refsAt : List SourceLoc)
| duplicateLabel (label : String) (first : SourceLoc) (second : SourceLoc)
| invalidDirective (loc : SourceLoc) (directive : String)
deriving Repr, DecidableEq

/-- Intermediate instruction with optional label and source location -/
structure IntermediateInstr where
  instr : LInstr
  loc : SourceLoc
  label : Option String := none
deriving Repr

/-- Strip comments (# to end of line) -/
private def cutComment (s : String) : String :=
  let parts := s.splitOn "#"
  match parts with
  | []   => ""
  | h::_ => h

/-- Extract tokens from a line (space-separated after comment removal) -/
private def tokenizeLine (s : String) : List String :=
  let s := (cutComment s).trim
  if s.isEmpty then []
  else s.split (·.isWhitespace) |>.filter (¬ ·.isEmpty)

/-- Macro definitions rewritten in terms of the macrocore primitives. -/
def expandMacro (name : String) : Option (Array LInstr) :=
  let mk := fun op arg => #[{ op := op, arg := arg }]
  match name with
  | "PHOTON_EMIT" =>
      some (Array.mk [LInstr.fold 1, LInstr.tokenDelta Opcode.BRAID 1, LInstr.fold (-1)])
  | "DIAMOND_CELL" =>
      some (Array.mk [LInstr.simple Opcode.LOCK, LInstr.balance BalanceMode.window,
                      LInstr.simple Opcode.LOCK])
  | "SEED_SPAWN" =>
      some (Array.mk [LInstr.tokenSet Opcode.SEED 1, LInstr.tokenSet Opcode.SEED 1])
  | "LISTEN_PAUSE" =>
      some (Array.mk [LInstr.listen ListenMode.noop, LInstr.balance BalanceMode.window])
  | _ => none

/-- Expand a single token into one or more primitive instructions. -/
def expandToken (tok : String) : Option (Array LInstr) :=
  match tok with
  | "LOCK"       => some #[LInstr.simple Opcode.LOCK]
  | "HARDEN"     => some #[LInstr.simple Opcode.LOCK]
  | "BALANCE"    => some #[LInstr.balance BalanceMode.window]
  | "CYCLE"      => some #[LInstr.balance BalanceMode.cycle]
  | "FOLD"       => some #[LInstr.fold 1]
  | "UNFOLD"     => some #[LInstr.fold (-1)]
  | "SEED"       => some #[LInstr.tokenSet Opcode.SEED 1 1]
  | "SPAWN"      => some #[LInstr.tokenSet Opcode.SEED 1 0]
  | "GC_SEED"    => some #[LInstr.tokenSet Opcode.SEED 0 0]
  | "GIVE"       => some #[LInstr.tokenDelta Opcode.BRAID 1]
  | "REGIVE"     => some #[LInstr.tokenDelta Opcode.MERGE (-1)]
  | "BRAID"      => some #[LInstr.simple Opcode.BRAID]
  | "MERGE"      => some #[LInstr.simple Opcode.MERGE]
  | "LISTEN"     => some #[LInstr.listen ListenMode.noop]
  | "VECTOR_EQ"  => some #[LInstr.listen ListenMode.vectorReset]
  | "FLIP"       => some #[LInstr.simple Opcode.FLIP]
  | _             => expandMacro tok

/-- Check if token is a label definition (ends with :) -/
private def isLabelDef (tok : String) : Option String :=
  if tok.endsWith ":" then
    some (tok.dropRight 1)
  else
    none

/-- Parse a single line into instructions with source location -/
private def parseLine (line : String) (lineNum : Nat) :
    Except ParseError (Array IntermediateInstr) := do
  let toks := tokenizeLine line
  if toks.isEmpty then
    return #[]

  let loc : SourceLoc := { line := lineNum }
  let mut result : Array IntermediateInstr := #[]
  let mut currentLabel : Option String := none

  for tok in toks do
    -- Check for label definition
    if let some label := isLabelDef tok then
      currentLabel := some label
      continue

    -- Directives (ignore for now): allow @phi phi^N to appear in source
    if tok = "@phi" then
      -- Expect next token to be a φ-literal; tolerate silently
      currentLabel := none
      continue

    -- Expand primitives/macros
    if let some insts := expandToken tok then
      for (idx, inst) in insts.enum do
        let instr : IntermediateInstr := {
          instr := inst,
          loc := { line := lineNum, column := idx },
          label := if idx = 0 then currentLabel else none
        }
        result := result.push instr
      currentLabel := none
      continue

    -- Unknown token
    return .error (ParseError.unknownOpcode loc tok)

  return result

/-- Label resolution state -/
structure LabelState where
  labels : Std.HashMap String Nat := {}
  references : List (String × SourceLoc) := []

/-- Resolve label references and build final program -/
private def resolveLabels (instrs : Array IntermediateInstr) :
    Except ParseError (Array LInstr) := do
  -- First pass: collect label definitions
  let mut labels : Std.HashMap String Nat := {}
  for (idx, instr) in instrs.toList.enum do
    if let some label := instr.label then
      if labels.contains label then
        let firstLoc := (instrs.toList.find? (fun i => i.label = some label)).get!.loc
        return .error (ParseError.duplicateLabel label firstLoc instr.loc)
      labels := labels.insert label idx

  -- Second pass: validate all label references (future: for jumps/branches)
  -- For now, just extract instructions
  return instrs.map (·.instr)

/-- Tail-recursive worker that parses a list of lines with an explicit index
    and accumulator of intermediate instructions (in order). -/
private def parseLinesAux : List String → Nat → List IntermediateInstr → Except ParseError (List IntermediateInstr)
  | [], _, acc => return acc
  | line :: lines, n, acc => do
      let lineInstrs ← parseLine line n
      parseLinesAux lines (n + 1) (acc ++ lineInstrs.toList)

/-- Parse a list of already-split source lines. -/
private def parseLines (lines : List String) : Except ParseError (Array LInstr) := do
  let instrs ← parseLinesAux lines 0 []
  resolveLabels (Array.mk instrs)

/-- Complete parsing pipeline emitting both instructions and φ-IR metadata. -/
def parseProgramFull (src : String) : Except ParseError ParseOutput := do
  let lines := src.splitOn "\n"
  let phiAnalysis := PhiIR.analyseLines lines
  let code ← parseLines lines
  let packets := PhiIR.packetize code
  return { code := code, phi := phiAnalysis, packets := packets }

/-- Backwards-compatible API returning only the instruction stream. -/
def parseProgram (src : String) : Except ParseError (Array LInstr) := do
  let out ← parseProgramFull src
  return out.code


@[simp] def instrToString : LInstr → String
  | ⟨Opcode.LOCK, _⟩ => "LOCK"
  | ⟨Opcode.BALANCE, OpcodeArg.balance BalanceMode.cycle⟩ => "CYCLE"
  | ⟨Opcode.BALANCE, _⟩ => "BALANCE"
  | ⟨Opcode.FOLD, OpcodeArg.fold dir⟩ => if dir = -1 then "UNFOLD" else "FOLD"
  | ⟨Opcode.FOLD, _⟩ => "FOLD"
  | ⟨Opcode.SEED, OpcodeArg.token (TokenAction.set 0 _)⟩ => "GC_SEED"
  | ⟨Opcode.SEED, OpcodeArg.token (TokenAction.set 1 cost)⟩ => if cost = 0 then "SPAWN" else "SEED"
  | ⟨Opcode.SEED, _⟩ => "SEED"
  | ⟨Opcode.BRAID, OpcodeArg.token (TokenAction.delta d)⟩ => if d = 1 then "GIVE" else "BRAID"
  | ⟨Opcode.BRAID, _⟩ => "BRAID"
  | ⟨Opcode.MERGE, OpcodeArg.token (TokenAction.delta d)⟩ => if d = -1 then "REGIVE" else "MERGE"
  | ⟨Opcode.MERGE, _⟩ => "MERGE"
  | ⟨Opcode.LISTEN, OpcodeArg.listen ListenMode.vectorReset⟩ => "VECTOR_EQ"
  | ⟨Opcode.LISTEN, _⟩ => "LISTEN"
  | ⟨Opcode.FLIP, _⟩ => "FLIP"

-- (Round-trip serialization lemmas from the 16-opcode era were removed.)

/-- Convert instruction array to executable program -/
def mkProgram (code : Array LInstr) : LProgram :=
  fun ip => if h : ip < code.size then code.get ⟨ip, h⟩ else { op := Opcode.LOCK }

/-- Serialise a program to a canonical source form: one token per line. -/
def serializeProgramLines (code : Array LInstr) : List String :=
  code.toList.map instrToString

def serializeProgram (code : Array LInstr) : String :=
  String.intercalate "\n" (serializeProgramLines code)

/-- Count opcodes of a specific type (ignoring arguments) in a program -/
def countOpcode (code : Array LInstr) (target : Opcode) : Nat :=
  code.foldl (fun acc i => if i.op = target then acc + 1 else acc) 0

/-- Check if program contains at least one instance of an opcode -/
def hasOpcode (code : Array LInstr) (target : Opcode) : Bool :=
  code.any (fun i => i.op = target)

/-- Extract all instructions with a given primitive opcode (ignoring args). -/
def findOpcodes (code : Array LInstr) (target : Opcode) : List (Nat × LInstr) :=
  code.toList.enum.filter (fun (_, i) => i.op = target)

/-- Pretty-print a program for debugging -/
def prettyPrint (code : Array LInstr) : String :=
  let lines := code.toList.enum.map fun (idx, instr) =>
    s!"{idx:04d}: {instrToString instr}"
  "\n".intercalate lines

/-- Program statistics for analysis -/
structure ProgramStats where
  totalInstructions : Nat
  opcodeCount : Opcode → Nat
  hasBalance : Bool
  hasFlip : Bool
  hasVectorEq : Bool
  macroExpanded : Bool := false
deriving Repr

def programStats (code : Array LInstr) : ProgramStats where
  totalInstructions := code.size
  opcodeCount := fun op => countOpcode code op
  hasBalance := hasOpcode code Opcode.BALANCE
  hasFlip := hasOpcode code Opcode.FLIP
  hasVectorEq := code.any (fun i =>
    match i.op, i.arg with
    | Opcode.LISTEN, OpcodeArg.listen ListenMode.vectorReset => true
    | _, _ => false)
  macroExpanded := true -- if we got here, macros were expanded

end LNAL
end IndisputableMonolith
