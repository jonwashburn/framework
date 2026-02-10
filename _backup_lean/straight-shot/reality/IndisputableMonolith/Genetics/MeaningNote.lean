import IndisputableMonolith.Genetics.Basic

namespace IndisputableMonolith
namespace Genetics

open Water

/-!
# Genetics.MeaningNote

A tiny “same note across layers” artifact:

- Meaning: `Water.WTokenSpec`
- Biology: `Water.AminoAcid`
- DNA: `Genetics.Codon`

This is a **structural** bridge: it composes already-defined maps and proves the
decode property in Lean. It makes no empirical claim beyond the (already encoded)
universal genetic code definition.
-/

/-- A single note traced across meaning → biology → DNA. -/
structure MeaningNote where
  /-- Semantic atom (WTokens). -/
  wtoken : Water.WTokenSpec
  /-- Corresponding amino acid. -/
  amino : Water.AminoAcid
  /-- A representative codon encoding that amino acid. -/
  codon : Codon
  /-- The amino acid field matches the canonical WToken→AA map. -/
  amino_eq : amino = Water.wtoken_to_amino wtoken
  /-- The representative codon decodes to the amino acid. -/
  decodes : genetic_code codon = CodonOutput.amino amino

/-- Canonical note construction from a WToken (WTokens → AA → Codon). -/
def noteOfWToken (w : Water.WTokenSpec) : MeaningNote :=
  { wtoken := w
  , amino := Water.wtoken_to_amino w
  , codon := codon_of_wtoken w
  , amino_eq := rfl
  , decodes := by
      simpa using genetic_code_codon_of_wtoken w }

/-- Canonical note construction from an amino acid (AA → WToken → Codon → AA). -/
def noteOfAmino (aa : Water.AminoAcid) : MeaningNote :=
  { wtoken := Water.amino_to_wtoken aa
  , amino := aa
  , codon := codon_of_wtoken (Water.amino_to_wtoken aa)
  , amino_eq := (Water.wtoken_to_amino_rightInverse aa).symm
  , decodes := by
      simpa using genetic_code_roundtrip_amino_via_wtoken aa }

end Genetics
end IndisputableMonolith
