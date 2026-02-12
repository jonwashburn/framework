import Mathlib
import IndisputableMonolith.Biology.PerfectGeneticCode

namespace IndisputableMonolith
namespace Verification
namespace PerfectGeneticCode

open Biology.PerfectGeneticCode

/-- Certificate for the Perfect Genetic Code Theorem. -/
structure PerfectGeneticCodeCert where
  deriving Repr

@[simp] def PerfectGeneticCodeCert.verified (_c : PerfectGeneticCodeCert) : Prop :=
  -- 20 amino acids match 20 WTokens
  numAminoAcids = 20 ∧
  -- Correspondence is isomorphic
  Nonempty (Fin 20 ≃ Token.WTokenId)

@[simp] theorem PerfectGeneticCodeCert.verified_any (c : PerfectGeneticCodeCert) :
    PerfectGeneticCodeCert.verified c := by
  constructor
  · rfl
  · have h := amino_acid_wtoken_isomorphism
    -- Need to show Fin numAminoAcids ≃ WTokenId implies Fin 20 ≃ WTokenId
    unfold numAminoAcids at h
    exact h

end PerfectGeneticCode
end Verification
end IndisputableMonolith
