import Mathlib
import IndisputableMonolith.LightLanguage.Meaning.MotifAlgebra
import IndisputableMonolith.LightLanguage.Meaning.LNALFactorization
import IndisputableMonolith.Ethics.Soul.Character
import IndisputableMonolith.Ethics.Virtues.Generators
import IndisputableMonolith.Ethics.Virtues.NormalForm

/-
# Ethics Bridge — Virtue Signatures to ULL Meanings

This module implements Step 5 of the ULL semantic plan.  We expose the data
structures that relate SoulCharacter virtue signatures to canonical ULL motifs
and prove schematic correspondence lemmas.  The constructions are intentionally
general: a `VirtueLabeler` describes how a SoulCharacter records virtues, a
`VirtueMotifConstraint` records the motif a virtue must manifest, and
`respectsConstraints` captures the compatibility predicate between a
SoulCharacter and a ULL meaning.  Compatibility is shown to be stable under
LNAL program execution via the factorisation developed in Step 4.
-/
namespace LightLanguage
namespace Meaning

open LightLanguage LNAL
open IndisputableMonolith
open IndisputableMonolith.Ethics
open IndisputableMonolith.Ethics.Soul
open IndisputableMonolith.Ethics.Virtues

/-- Assigns a canonical primitive label to every virtue appearing in a
`VirtueSignature`.  Concrete systems can instantiate this by projecting a
SoulCharacter audit record to the primitive enumerator. -/
structure VirtueLabeler where
  label : Generators.Virtue → Primitive

/-- A virtue-level motif requirement: whenever the associated primitive appears
in the virtue signature, the ULL meaning must realise the provided motif. -/
structure VirtueMotifConstraint where
  primitive : Primitive
  motif : Motif
  narrative : String := ""

namespace VirtueMotifConstraint

/-- Trigger predicate: a constraint is triggered when its primitive is present
in the virtue signature (after labelling). -/
def triggered (L : VirtueLabeler) (c : VirtueMotifConstraint)
    (signature : VirtueSignature) : Prop :=
  ∃ v ∈ signature.components, L.label v = c.primitive

/-- Satisfaction predicate: the constraint holds for a meaning when the
required motif matches the meaning. -/
def satisfied (c : VirtueMotifConstraint) (meaning : CanonicalMeaning) : Prop :=
  c.motif.matches meaning

end VirtueMotifConstraint

/-- SoulCharacter compatibility with a list of constraints. -/
def respectsConstraints (L : VirtueLabeler)
    (constraints : List VirtueMotifConstraint)
    (signature : VirtueSignature) (meaning : CanonicalMeaning) : Prop :=
  ∀ c ∈ constraints,
    VirtueMotifConstraint.triggered L c signature →
    VirtueMotifConstraint.satisfied c meaning

/-- Convenience wrapper for SoulCharacters. -/
def soulRespectsMeaning {AgentId BondId}
    (L : VirtueLabeler)
    (constraints : List VirtueMotifConstraint)
    (sc : SoulCharacter AgentId BondId)
    (meaning : CanonicalMeaning) : Prop :=
  respectsConstraints L constraints sc.virtueSignature meaning

/-! ## Canonical motif constraints -/

namespace CanonicalConstraints

private def triad012 : Fin 3 → ℕ
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 2

private def loveSequence : LNALSequence :=
  [LNALOp.lock [], LNALOp.braid triad012, LNALOp.lock []]

private def justiceSequence : LNALSequence :=
  [LNALOp.braid triad012, LNALOp.lock [0], LNALOp.balance []]

private def compassionSequence : LNALSequence :=
  [LNALOp.listen, LNALOp.fold [], LNALOp.lock []]

private def temperanceSequence : LNALSequence :=
  [LNALOp.listen, LNALOp.lock [], LNALOp.balance []]

private def patienceSequence : LNALSequence :=
  [LNALOp.listen, LNALOp.listen, LNALOp.lock []]

private def gratitudeSequence : LNALSequence :=
  [LNALOp.listen, LNALOp.fold [], LNALOp.balance []]

private def humilitySequence : LNALSequence :=
  [LNALOp.balance [], LNALOp.lock []]

private def hopeSequence : LNALSequence :=
  [LNALOp.listen, LNALOp.braid triad012]

private def prudenceSequence : LNALSequence :=
  [LNALOp.balance [0], LNALOp.balance [1], LNALOp.lock []]

private def sacrificeSequence : LNALSequence :=
  [LNALOp.lock [0], LNALOp.fold [0], LNALOp.balance []]

private def courageSequence : LNALSequence :=
  [LNALOp.braid triad012, LNALOp.lock []]

/-- Love demands symmetric exchange: lock → braid → lock. -/
def loveConstraint : VirtueMotifConstraint :=
  { primitive := Primitive.Love
    motif := Motif.seq (Motif.ofSequence loveSequence) (Motif.ofSequence [])
    narrative := "Love manifests as a symmetric lock/braid/lock motif." }

/-- Justice demands a braid posting followed by a balancing lock. -/
def justiceConstraint : VirtueMotifConstraint :=
  { primitive := Primitive.Justice
    motif := Motif.seq (Motif.ofSequence justiceSequence) (Motif.ofSequence [])
    narrative := "Justice manifests as a braid posting closed by a lock." }

/-- Compassion requires listen/fold relief before returning to lock. -/
def compassionConstraint : VirtueMotifConstraint :=
  { primitive := Primitive.Compassion
    motif := Motif.ofSequence compassionSequence
    narrative := "Compassion manifests as listen→fold relief within a lock envelope." }

/-- Temperance pins a listen→lock→balance sequence inside the BIOPHASE window. -/
def temperanceConstraint : VirtueMotifConstraint :=
  { primitive := Primitive.Temperance
    motif := Motif.ofSequence temperanceSequence
    narrative := "Temperance appears as listen/lock/balance, encoding φ-budget moderation." }

/-- Patience enforces consecutive listen windows before the lock executes. -/
def patienceConstraint : VirtueMotifConstraint :=
  { primitive := Primitive.Patience
    motif := Motif.ofSequence patienceSequence
    narrative := "Patience shows two listen windows then a lock (8-tick wait)." }

/-- Gratitude folds cooperation evidence before rebalancing the ledger. -/
def gratitudeConstraint : VirtueMotifConstraint :=
  { primitive := Primitive.Gratitude
    motif := Motif.ofSequence gratitudeSequence
    narrative := "Gratitude is recorded as listen→fold→balance at φ-rate." }

/-- Humility re-balances σ before locking the new self-model. -/
def humilityConstraint : VirtueMotifConstraint :=
  { primitive := Primitive.Humility
    motif := Motif.ofSequence humilitySequence
    narrative := "Humility manifests as balance→lock (σ correction)." }

/-- Hope injects a braid after a listen window, pointing toward the optimistic branch. -/
def hopeConstraint : VirtueMotifConstraint :=
  { primitive := Primitive.Hope
    motif := Motif.seq (Motif.ofSequence hopeSequence) (Motif.ofSequence [])
    narrative := "Hope presents as listen→braid, nudging the projection channel." }

/-- Prudence uses a double balance before committing to lock. -/
def prudenceConstraint : VirtueMotifConstraint :=
  { primitive := Primitive.Prudence
    motif := Motif.ofSequence prudenceSequence
    narrative := "Prudence double-balances variance before locking a choice." }

/-- Sacrifice folds a locked channel to absorb skew. -/
def sacrificeConstraint : VirtueMotifConstraint :=
  { primitive := Primitive.Sacrifice
    motif := Motif.ofSequence sacrificeSequence
    narrative := "Sacrifice is lock→fold→balance, transferring energy at φ efficiency." }

/-- Courage braids and immediately locks, representing decisive high-gradient action. -/
def courageConstraint : VirtueMotifConstraint :=
  { primitive := Primitive.Courage
    motif := Motif.ofSequence courageSequence
    narrative := "Courage is captured as braid→lock on the σ-graph." }

/-- Default constraint catalogue covering the primary relational/systemic trio. -/
def catalogue : List VirtueMotifConstraint :=
  [ loveConstraint
  , justiceConstraint
  , compassionConstraint
  , temperanceConstraint
  , patienceConstraint
  , gratitudeConstraint
  , humilityConstraint
  , hopeConstraint
  , prudenceConstraint
  , sacrificeConstraint
  , courageConstraint
  ]

@[simp] lemma love_mem_catalogue :
    loveConstraint ∈ catalogue := by simp [catalogue]

@[simp] lemma justice_mem_catalogue :
    justiceConstraint ∈ catalogue := by simp [catalogue]

@[simp] lemma compassion_mem_catalogue :
    compassionConstraint ∈ catalogue := by simp [catalogue]

@[simp] lemma temperance_mem_catalogue :
    temperanceConstraint ∈ catalogue := by simp [catalogue]

@[simp] lemma patience_mem_catalogue :
    patienceConstraint ∈ catalogue := by simp [catalogue]

@[simp] lemma gratitude_mem_catalogue :
    gratitudeConstraint ∈ catalogue := by simp [catalogue]

@[simp] lemma humility_mem_catalogue :
    humilityConstraint ∈ catalogue := by simp [catalogue]

@[simp] lemma hope_mem_catalogue :
    hopeConstraint ∈ catalogue := by simp [catalogue]

@[simp] lemma prudence_mem_catalogue :
    prudenceConstraint ∈ catalogue := by simp [catalogue]

@[simp] lemma sacrifice_mem_catalogue :
    sacrificeConstraint ∈ catalogue := by simp [catalogue]

@[simp] lemma courage_mem_catalogue :
    courageConstraint ∈ catalogue := by simp [catalogue]

end CanonicalConstraints

/-- Controlled environments guarantee that motif evidence can be mapped back to virtues. -/
def controlledEnvironment
    (L : VirtueLabeler)
    (signature : VirtueSignature)
    (meaning : CanonicalMeaning) : Prop :=
  ∀ {c : VirtueMotifConstraint},
    c ∈ CanonicalConstraints.catalogue →
    VirtueMotifConstraint.satisfied c meaning →
    ∃ v ∈ signature.components, L.label v = c.primitive

-/-- Motif preservation lemma: if an LNAL program preserves a motif on
canonical sequences, it preserves satisfaction on meanings. -/
lemma motif_preserved_by_prog
    (prog : Prog) (motif : Motif)
    (h : ∀ seq, motif.carrier seq → motif.carrier (prog.evalSequence seq))
    {meaning : CanonicalMeaning}
    (hsat : motif.matches meaning) :
    motif.matches (prog.act meaning) := by
  unfold Motif.matches at *
  have := h _ hsat
  simpa [Prog.act, Prog.evalSequence, canonicalSequence_act] using this

/-- When every constraint motif is preserved by a program, compatibility with a
SoulCharacter signature is preserved under the program's action. -/
lemma respects_after_prog
    (prog : Prog)
    (constraints : List VirtueMotifConstraint)
    (L : VirtueLabeler)
    {signature : VirtueSignature}
    {meaning : CanonicalMeaning}
    (preserve :
      ∀ c ∈ constraints,
        ∀ seq, c.motif.carrier seq → c.motif.carrier (prog.evalSequence seq))
    (hres : respectsConstraints L constraints signature meaning) :
    respectsConstraints L constraints signature (prog.act meaning) := by
  intro c hc htrig
  have hmotif := hres c hc htrig
  exact
    motif_preserved_by_prog prog c.motif
      (preserve c hc) hmotif

/-- Schematic correspondence: if the catalogue is satisfied, any triggered
constraint produces its motif on the meaning. -/
lemma triggered_implies_matches
    (L : VirtueLabeler)
    (signature : VirtueSignature)
    (meaning : CanonicalMeaning)
    (hres :
      respectsConstraints L CanonicalConstraints.catalogue signature meaning)
    {c : VirtueMotifConstraint}
    (hc : c ∈ CanonicalConstraints.catalogue)
    (htrig : VirtueMotifConstraint.triggered L c signature) :
    VirtueMotifConstraint.satisfied c meaning :=
  hres c hc htrig

/-- Forward correspondence: every virtue in the signature produces its canonical motif. -/
theorem virtue_implies_motif
    (L : VirtueLabeler)
    (signature : VirtueSignature)
    (meaning : CanonicalMeaning)
    (hres :
      respectsConstraints L CanonicalConstraints.catalogue signature meaning)
    (hcover :
      ∀ v : Generators.Virtue,
        ∃ c ∈ CanonicalConstraints.catalogue, L.label v = c.primitive)
    {v : Generators.Virtue}
    (hmem : v ∈ signature.components) :
    ∃ c ∈ CanonicalConstraints.catalogue,
      L.label v = c.primitive ∧
      VirtueMotifConstraint.satisfied c meaning := by
  classical
  rcases hcover v with ⟨c, hc, hlabel⟩
  refine ⟨c, hc, hlabel, ?_⟩
  exact hres c hc ⟨v, hmem, hlabel⟩

/-- Reverse correspondence inside controlled environments. -/
theorem motif_implies_virtue_context
    (L : VirtueLabeler)
    (signature : VirtueSignature)
    (meaning : CanonicalMeaning)
    (hctx : controlledEnvironment L signature meaning)
    {c : VirtueMotifConstraint}
    (hc : c ∈ CanonicalConstraints.catalogue)
    (hsat : VirtueMotifConstraint.satisfied c meaning) :
    ∃ v ∈ signature.components, L.label v = c.primitive :=
  hctx hc hsat

end Meaning
end LightLanguage
