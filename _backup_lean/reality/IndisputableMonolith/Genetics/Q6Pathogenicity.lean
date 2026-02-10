import Mathlib
import IndisputableMonolith.Genetics.QualiaOptimization

/-!
# Q₆ Pathogenicity (ClinVar → VEP → Q₆)

This module provides Lean-side *definitions* for expressing Q₆-distance based
pathogenicity hypotheses, plus explicitly-marked empirical placeholders.

AUDIT NOTE (2025-12-20):
- The statistical validation of E4 relies on external datasets (ClinVar + Ensembl VEP)
  and is therefore represented here as *axioms* / bridge statements, not theorems.
- Any “confirmed” status is **pipeline-scoped**: it applies to the explicit filters,
  sampling scheme, and analysis protocol described in `OCTAVE_DNA_OPERATIONAL_PLAN.md`
  and summarized in `Source-Super-rrf.txt`.

Core empirical summary (pipeline-scoped, not proved in Lean):
- Tier-3 preregistered confirm sweep (seeds 20251229..20251233) passes the locked stability
  rule: all Mann–Whitney z>0 and Stouffer combined z ≈ 6.155 (one-tailed p ≈ 3.8e-10).

See:
- `tools/clinvar_q6_pipeline.py`
- `tools/q6_dataset_stats.py`
- `data/clinvar_q6_tier3_confirm_seed*.jsonl`
- `OCTAVE_DNA_OPERATIONAL_PLAN.md` (E4 protocol)
-/

namespace IndisputableMonolith
namespace Genetics
namespace Q6Pathogenicity

open QualiaOptimization

/-! ## Labels and records -/

/-- Coarse ClinVar-style label for our two-bucket test. -/
inductive ClinLabel : Type
  | pathogenic
  | benign
deriving DecidableEq, Repr

/-- A codon-level missense record: wild-type codon → mutant codon with a label. -/
structure CodonVariant where
  ref : Codon
  alt : Codon
  label : ClinLabel
deriving Repr

/-! ## Q₆ distance for a codon variant -/

/-- Q₆ distance between the reference and alternate codon, using the
`codon_to_qualia` embedding from `QualiaOptimization`. -/
def q6_distance (v : CodonVariant) : ℕ :=
  qualia_distance (codon_to_qualia v.ref) (codon_to_qualia v.alt)

/-- Extract all Q₆ distances for a specific label within a dataset. -/
def distances (ds : List CodonVariant) (lbl : ClinLabel) : List ℕ :=
  (ds.filter (fun r => r.label = lbl)).map q6_distance

/-! ## Simple effect predicates (definitions, not claims) -/

/-- Mean of a list of naturals, coerced to ℝ.

Note: `xs.length = 0` yields `0` by field convention (`(0 : ℝ)⁻¹ = 0`), which is fine
for a total definition but analyses should use datasets with both labels present. -/
noncomputable def meanNat (xs : List ℕ) : ℝ :=
  (xs.sum : ℝ) / (xs.length : ℝ)

/-- Mean Q₆ distance for a label in a dataset. -/
noncomputable def meanDistance (ds : List CodonVariant) (lbl : ClinLabel) : ℝ :=
  meanNat (distances ds lbl)

/-- E4 (weak form): mean pathogenic Q₆ distance exceeds mean benign Q₆ distance. -/
noncomputable def supports_E4_mean (ds : List CodonVariant) : Prop :=
  meanDistance ds .pathogenic > meanDistance ds .benign

/-! ## Empirical placeholders (bridge axioms) -/

/-- Bundle type for an externally-validated tier-3 confirm-sweep report.

This file intentionally does **not** assert that such a report exists; the Python
pipeline produces artifacts that can later be mapped into this structure (or a
Lean-checkable certificate format).
-/
structure Tier3ConfirmSweepReport where
  /-- The per-seed datasets included in the confirm sweep. -/
  datasets : List (List CodonVariant)
  /-- Directional pass: every dataset supports E4 in the mean-direction sense. -/
  directional :
    ∀ ds, List.Mem ds datasets → supports_E4_mean ds
  /-- Aggregate (Stouffer) z-score for the confirm sweep. -/
  stouffer_z : ℝ
  /-- Preregistered one-tailed pass condition: z > 1.645. -/
  stouffer_pass : stouffer_z > 1.645

end Q6Pathogenicity
end Genetics
end IndisputableMonolith
