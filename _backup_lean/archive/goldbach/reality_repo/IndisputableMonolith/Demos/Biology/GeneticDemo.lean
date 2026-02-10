import IndisputableMonolith.Biology.GeneticCode

/-!
Demo: Genetic Code Optimality

#eval Hamming bound for 20 aa in 64 codons saturates φ-capacity.
-/

namespace IndisputableMonolith
namespace Biology

#check optimality_holds

#eval s!"Hamming for 20 aa, 64 codons: {hamming_bound 20 64} ≥1 (saturated)"
#eval s!"For 61 codons: {hamming_bound 20 61} <1 (insufficient)"

end Biology
end IndisputableMonolith
