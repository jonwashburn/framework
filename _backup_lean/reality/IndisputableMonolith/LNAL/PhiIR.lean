import Mathlib
import Std.Data.HashMap
import IndisputableMonolith.Constants
import IndisputableMonolith.LNAL.Opcodes

namespace IndisputableMonolith
namespace LNAL
namespace PhiIR

open Std
open LNAL

/-! # φ-IR Literal Analysis

Provides parsing and analysis utilities for log-φ literals that appear in
LNAL assembler sources. Literals are written as directives such as
`@phi phi^3` or `@phi frequency phi^-2` and are interpreted as logarithms
base φ. We expose:

* Zeckendorf decomposition of exponents (for φ-invariant encodings)
* Exact real value accessors (`φ^n`), with reciprocal symmetry helpers
* Source analysis that tracks duplicate labels and malformed directives

The goal is to make φ-symmetric numerics first-class without requiring a
full assembler rewriter. Downstream passes (compiler, manifest, runtime)
consume the `PhiAnalysis` structure emitted here.
-/

/-! ## Utilities -/

/-- Remove comments starting with `#` and trim whitespace. -/
private def stripComment (line : String) : String :=
  match line.splitOn "#" with
  | []      => ""
  | part::_ => (part.trimAscii).toString

/-- Tokenise a line on whitespace (after comment stripping). -/
private def tokenize (line : String) : List String :=
  let core := stripComment line
  if core.isEmpty then []
  else
    -- Std's `String.split` now produces an iterator of `String.Slice`; normalize to spaces and use `splitOn`.
    let normalized := core.map (fun c => if c.isWhitespace then ' ' else c)
    normalized.splitOn " " |>.filter (fun s => ¬ s.isEmpty)

/-- Fibonacci numbers with F₀ = 0, F₁ = 1. -/
def fibonacci : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+2 => fibonacci (n+1) + fibonacci n

private def fibIndicesUpTo (n : Nat) : List Nat :=
  (List.range (n + 2)).filter (fun k => fibonacci k ≤ n)

/-- Zeckendorf decomposition of a natural number. -/
def zeckendorfNat (n : Nat) : List Nat :=
  let (_, acc) :=
    (fibIndicesUpTo n).reverse.foldl
      (fun (state : Nat × List Nat) idx =>
        let (remaining, selected) := state
        if fibonacci idx ≤ remaining then
          (remaining - fibonacci idx, idx :: selected)
        else
          (remaining, selected))
      (n, [])
  acc.reverse

/-- Zeckendorf decomposition of an integer (on absolute value). -/
def zeckendorfInt (z : Int) : List Nat :=
  zeckendorfNat z.natAbs

/-- Pretty-print a Zeckendorf decomposition as `F_k + F_j + …`. -/
def zeckendorfString (indices : List Nat) : String :=
  match indices.map (fun k => s!"F_{k}") with
  | [] => "0"
  | items => String.intercalate " + " items

/-! ## Literal representation -/

structure PhiLiteral where
  /-- Source line number (0-indexed). -/
  line : Nat
  /-- Optional symbolic name (`@phi name phi^N`). -/
  name : Option String := none
  /-- Exponent `N` in `φ^N`. -/
  exponent : Int
  /-- Original literal text (after trimming, without comments). -/
  raw : String := ""
  /-- Zeckendorf decomposition of `|N|`. -/
  zeckendorf : List Nat := []
deriving Repr, DecidableEq

namespace PhiLiteral

noncomputable def value (lit : PhiLiteral) : ℝ :=
  IndisputableMonolith.Constants.phi ^ lit.exponent

noncomputable def reciprocalValue (lit : PhiLiteral) : ℝ :=
  IndisputableMonolith.Constants.phi ^ (-lit.exponent)

/-- Human-readable summary for diagnostics. -/
noncomputable def summary (lit : PhiLiteral) : String :=
  let nameStr := lit.name.getD "<unnamed>"
  let sign := if lit.exponent < 0 then "-" else ""
  let expDisplay := s!"{sign}φ^{lit.exponent.natAbs}"
  s!"{nameStr}@{lit.line}: {expDisplay} (Zeckendorf {zeckendorfString lit.zeckendorf})"

end PhiLiteral

/-! ## Directive parsing -/

/-- Parse a literal token of the form `phi^N` or `φ^N`. -/
def parsePhiPow (tok : String) : Option Int :=
  let t := (tok.trimAscii).toString
  let lower := t.map Char.toLower
  if lower.startsWith "phi^" ∨ lower.startsWith "φ^" then
    let parts := lower.splitOn "^"
    match parts with
    | [_base, exp] =>
        if exp.toList.all (fun c => c.isDigit || c = '-' || c = '+') then
          exp.toInt?
        else none
    | _ => none
  else none

/-- Helper recognising directives of the form `@phi ...`. -/
def parsePhiDirectiveTokens (tokens : List String) : Option (Option String × Except String Int) :=
  match tokens with
  | [] => none
  | tok :: rest =>
      if (tok.trimAscii).toString ≠ "@phi" then none
      else
        match rest with
        | [] => some (none, .error "expected phi literal (phi^N)")
        | [val] =>
            some (none, match parsePhiPow val with
              | some n => .ok n
              | none => .error s!"invalid phi literal '{val}'")
        | name :: tail =>
            match tail with
            | "=" :: val :: _ =>
                some (name, match parsePhiPow val with
                  | some n => .ok n
                  | none => .error s!"invalid phi literal '{val}'")
            | val :: _ =>
                some (name, match parsePhiPow val with
                  | some n => .ok n
                  | none => .error s!"invalid phi literal '{val}'")
            | _ => some (none, .error "malformed phi directive")

/-- Recognise the legacy `@phi phi^N` pattern (for backwards compatibility). -/
def isPhiDirective (tokens : List String) : Bool :=
  match parsePhiDirectiveTokens tokens with
  | some (_, .ok _) => true
  | _ => false

/-- Result of analysing `@phi` directives within a source file. -/
structure PhiAnalysis where
  literals : Array PhiLiteral := #[]
  errors   : Array (Nat × String) := #[]
  duplicateNames : List String := []
deriving Repr

/-- Check whether an instruction is a BALANCE opcode. -/
private def isBalanceInstr (instr : LInstr) : Bool :=
  instr.op == Opcode.BALANCE

/-- Net token delta contributed by an instruction. -/
private def tokenDeltaOfInstr (instr : LInstr) : Int :=
  if instr.op == Opcode.BRAID || instr.op == Opcode.MERGE then
    match instr.arg with
    | OpcodeArg.token (TokenAction.delta delta) => delta
    | _ => 0
  else 0

/-- Canonical Gray-code cycle for the 3-cube (length 8). -/
def grayCycle : Array (Fin 8) :=
  #[⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩, ⟨2, by decide⟩,
    ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨5, by decide⟩, ⟨4, by decide⟩]

/-- Gray-code index associated with window `w`. -/
def grayIndex (w : Nat) : Nat :=
  let idx : Fin 8 := ⟨w % 8, Nat.mod_lt _ (by decide)⟩
  (grayCycle[idx]!).val

/-- Summary of an eight-instruction window paired with its Gray index. -/
structure WindowPacket where
  window : Nat
  gray   : Nat
  length : Nat
  balanceCount : Nat
  netDelta : Int
  neutral : Bool
deriving Repr

/-- Packet-level analysis across the whole program. -/
structure PacketAnalysis where
  packets : List WindowPacket := []
  allNeutral : Bool := true
  errors : List String := []
deriving Repr

instance : Inhabited PacketAnalysis := ⟨{}⟩

private def analyseWindow (window : Array LInstr) (idx : Nat) : WindowPacket × List String :=
  let (balanceCount, netDelta) :=
    window.foldl
      (fun (acc : Nat × Int) (instr : LInstr) =>
        let (b, d) := acc
        let balanceInc : Nat := if isBalanceInstr instr then 1 else 0
        let deltaInc : Int := tokenDeltaOfInstr instr
        (b + balanceInc, d + deltaInc))
      (0, 0)
  let len := window.size
  let lenOk : Prop := len = 8
  let balOk : Prop := balanceCount > 0
  let deltaOk : Prop := netDelta = 0
  let neutral := decide lenOk && decide balOk && decide deltaOk
  let lengthErrors := if len ≠ 8 then [s!"φ-IR packet window {idx} has length {len} (expected 8)"] else []
  let balanceErrors := if balanceCount = 0 then [s!"φ-IR packet window {idx} missing BALANCE opcode"] else []
  let deltaErrors := if netDelta ≠ 0 then [s!"φ-IR packet window {idx} has net token delta {netDelta}"] else []
  let errs := lengthErrors ++ balanceErrors ++ deltaErrors
  let packet : WindowPacket := {
    window := idx,
    gray := grayIndex idx,
    length := len,
    balanceCount := balanceCount,
    netDelta := netDelta,
    neutral := neutral
  }
  (packet, errs)

/-- Build Gray-coded window packets with neutrality diagnostics. -/
def packetize (code : Array LInstr) : PacketAnalysis :=
  let windowCount := (code.size + 7) / 8
  if windowCount = 0 then
    { packets := [], allNeutral := true, errors := [] }
  else
    let initState : List WindowPacket × List String × Bool := ([], [], true)
    let (packetList, errorList, allNeutral) :=
      (List.range windowCount).foldl
        (fun (state : List WindowPacket × List String × Bool) (w : Nat) =>
          let (packets, errors, neutralFlag) := state
          let start := 8 * w
          let stop := min code.size (start + 8)
          let window := code.extract start stop
          let (packet, windowErrors) := analyseWindow window w
          (packet :: packets, errors ++ windowErrors, neutralFlag && packet.neutral))
        initState
    { packets := packetList.reverse,
      allNeutral := allNeutral,
      errors := errorList }

/-- Analyse a list of source lines for φ directives. -/
def analyseLines (lines : List String) : PhiAnalysis :=
  Id.run <| do
    let mut lits : Array PhiLiteral := #[]
    let mut errs : Array (Nat × String) := #[]
    let mut seen : HashMap String Nat := {}
    let mut dups : List String := []
    let mut idx : Nat := 0
    for line in lines do
      let tokens := tokenize line
      match parsePhiDirectiveTokens tokens with
      | none =>
          idx := idx + 1
          continue
      | some (name?, result) =>
          match result with
          | .error msg =>
              errs := errs.push (idx, msg)
          | .ok exponent =>
              let raw := stripComment line
              let zeck := zeckendorfInt exponent
              let literal : PhiLiteral := {
                line := idx,
                name := name?,
                exponent := exponent,
                raw := raw,
                zeckendorf := zeck
              }
              lits := lits.push literal
              if let some name := name? then
                if seen.contains name then
                  if ¬ dups.contains name then dups := name :: dups
                else
                  seen := seen.insert name idx
      idx := idx + 1
    pure { literals := lits, errors := errs, duplicateNames := dups.reverse }

/-- Analyse a complete source string (split on newlines). -/
def analyseSource (src : String) : PhiAnalysis :=
  analyseLines (src.splitOn "\n")

end PhiIR

end LNAL
end IndisputableMonolith

namespace IndisputableMonolith
namespace LNAL

export PhiIR (PhiLiteral PhiAnalysis PacketAnalysis WindowPacket analyseSource
  analyseLines parsePhiPow isPhiDirective zeckendorfNat zeckendorfInt
  zeckendorfString packetize grayIndex)

end LNAL
end IndisputableMonolith
