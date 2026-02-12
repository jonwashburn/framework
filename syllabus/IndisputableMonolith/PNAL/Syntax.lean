import Mathlib
import IndisputableMonolith.LNAL.Opcodes

/-!
# PNAL Abstract Syntax Tree

Defines the abstract syntax for PNAL (Protein Native Assembly Language),
a high-level domain-specific language that compiles to LNAL.

## Design Goals

1. **Type Safety**: Catch errors at compile time
2. **Protein-Specific**: Natural expressions for folding operations
3. **Provable Compilation**: Preserve LNAL invariants
4. **Human-Readable**: Clear correspondence to folding mechanisms

## Instruction Categories

- **Selection**: Choose residues, ranges, secondary structure
- **Torsions**: Rotate φ, ψ, ω, χ angles
- **Contacts**: Set/clear native contacts, H-bonds, salt bridges
- **Secondary**: Nucleate helices, turns, β-sheets
- **Core/Solvent**: Hydrophobic core packing, solvation
- **Measurement**: LISTEN, LOCK, BALANCE (phase-aware)
- **Guards**: Assertions for validation

## References

- `tools/pnal/README.md`: Language specification
- `Protein Folding as Phase Recognition.tex`: PNAL grammar and semantics
-/

namespace IndisputableMonolith
namespace PNAL

/-! ## Basic Types -/

/-- Residue index (1-based for biochemical convention) -/
abbrev ResidueId := Nat

/-- Residue range [start, end] inclusive -/
structure ResidueRange where
  start : ResidueId
  stop : ResidueId
  valid : start ≤ stop
deriving Repr, DecidableEq

/-- Secondary structure type -/
inductive SecondaryStructure where
  | helix
  | sheet
  | turn
  | coil
deriving Repr, DecidableEq

/-- β-strand pairing type -/
inductive BetaPairingType where
  | parallel
  | antiparallel
deriving Repr, DecidableEq

/-- Direction for helix propagation -/
inductive Direction where
  | NtoC  -- N-terminus to C-terminus
  | CtoN  -- C-terminus to N-terminus
deriving Repr, DecidableEq

/-- Proline conformation -/
inductive ProlineConf where
  | cis
  | trans
deriving Repr, DecidableEq

/-! ## Selection Instructions -/

inductive SelectionInstr where
  | selRes (i : ResidueId)
  | selRange (range : ResidueRange)
  | selSecStruct (ss : SecondaryStructure)
  | maskContact (i j : ResidueId)
deriving Repr

/-! ## Torsion Instructions -/

inductive TorsionInstr where
  | rotPhi (delta : Int)      -- Backbone φ rotation
  | rotPsi (delta : Int)      -- Backbone ψ rotation
  | rotOmega (conf : ProlineConf)  -- Peptide bond ω
  | rotChi (n : Nat) (delta : Int)  -- Side-chain χ_n rotation
  | sidechainPack                    -- Local side-chain repacking
deriving Repr

/-! ## Contact Instructions -/

inductive ContactInstr where
  | setContact (i j : ResidueId)
  | clearContact (i j : ResidueId)
  | setHBond (i j : ResidueId)
  | breakHBond (i j : ResidueId)
  | setSalt (i j : ResidueId)
  | setDisulfide (i j : ResidueId)
deriving Repr

/-! ## Secondary Structure Instructions -/

inductive SecondaryInstr where
  | nucleateHelix (range : ResidueRange)
  | propagateHelix (dir : Direction)
  | nucleateTurn (range : ResidueRange)  -- Typically 4 residues
  | pairBeta (range1 range2 : ResidueRange) (pairType : BetaPairingType)
deriving Repr

/-! ## Core/Solvent Instructions -/

inductive CoreSolventInstr where
  | nucleateCore (residues : List ResidueId)
  | packCore
  | solvateShell (enable : Bool)
  | screenPhase (mask : Nat)  -- Bit mask for phase screening
deriving Repr

/-! ## Measurement Instructions (Phase-Aware) -/

inductive MeasurementInstr where
  | listenPhase              -- Sample eight-beat IR phase
  | lockPhase                 -- Open ledger-neutral read window
  | balancePhase              -- Close read window
deriving Repr

/-! ## Guard Instructions -/

structure ContactAssertion where
  i : ResidueId
  j : ResidueId
  maxDist : Float  -- Ångströms
deriving Repr

structure RMSDAssertion where
  maxRMSD : Float  -- Ångströms
deriving Repr

inductive GuardInstr where
  | assertNoClash
  | assertContact (assertion : ContactAssertion)
  | assertRMSD (assertion : RMSDAssertion)
  | assertCisPro (i : ResidueId)
  | assertBeat (beatIndex : Nat) (bandName : String)
deriving Repr

/-! ## Wait Instruction -/

inductive WaitInstr where
  | waitTicks (n : Nat)
deriving Repr

/-! ## Complete PNAL Instruction -/

inductive PNALInstr where
  | selection (instr : SelectionInstr)
  | torsion (instr : TorsionInstr)
  | contact (instr : ContactInstr)
  | secondary (instr : SecondaryInstr)
  | coreSolvent (instr : CoreSolventInstr)
  | measurement (instr : MeasurementInstr)
  | guard (instr : GuardInstr)
  | wait (instr : WaitInstr)
  | comment (text : String)
deriving Repr

/-! ## PNAL Program -/

/-- A PNAL program is a sequence of instructions -/
structure PNALProgram where
  instructions : List PNALInstr
  metadata : Option String := none
deriving Repr

namespace PNALProgram

/-- Empty program -/
def empty : PNALProgram := ⟨[], none⟩

/-- Append instruction to program -/
def append (prog : PNALProgram) (instr : PNALInstr) : PNALProgram :=
  ⟨prog.instructions ++ [instr], prog.metadata⟩

/-- Program length -/
def length (prog : PNALProgram) : Nat :=
  prog.instructions.length

end PNALProgram

/-! ## Convenience Constructors -/

namespace PNALInstr

def selRes (i : ResidueId) : PNALInstr :=
  .selection (.selRes i)

def selRange (start stop : ResidueId) (h : start ≤ stop) : PNALInstr :=
  .selection (.selRange ⟨start, stop, h⟩)

def rotPhi (delta : Int) : PNALInstr :=
  .torsion (.rotPhi delta)

def rotPsi (delta : Int) : PNALInstr :=
  .torsion (.rotPsi delta)

def setContact (i j : ResidueId) : PNALInstr :=
  .contact (.setContact i j)

def nucleateHelix (start stop : ResidueId) (h : start ≤ stop) : PNALInstr :=
  .secondary (.nucleateHelix ⟨start, stop, h⟩)

def listenPhase : PNALInstr :=
  .measurement .listenPhase

def assertNoClash : PNALInstr :=
  .guard .assertNoClash

end PNALInstr

end PNAL
end IndisputableMonolith
