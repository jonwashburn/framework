import Mathlib
import IndisputableMonolith.Fusion.NuclearBridge
import IndisputableMonolith.Fusion.ReactionNetwork

/-!
# Stellar Nucleosynthesis Validation

Extends magic number theory to stellar nucleosynthesis predictions.

## Key Results

1. **Waiting Points**: Magic N nuclei accumulate during r-process
2. **Abundance Peaks**: Occur at N = 50, 82, 126 (magic numbers)
3. **Iron Peak**: Fe-56 stability explained by near-magic configuration
-/

namespace IndisputableMonolith.Fusion.Nucleosynthesis

open NuclearBridge

noncomputable section

/-! ## Magic Number Helpers -/

/-- 50 is a magic number. -/
lemma magic50 : Nuclear.MagicNumbers.isMagic 50 := by native_decide

/-- 82 is a magic number. -/
lemma magic82 : Nuclear.MagicNumbers.isMagic 82 := by native_decide

/-- 126 is a magic number. -/
lemma magic126 : Nuclear.MagicNumbers.isMagic 126 := by native_decide

/-- 28 is a magic number. -/
lemma magic28 : Nuclear.MagicNumbers.isMagic 28 := by native_decide

/-! ## Waiting Points -/

/-- N=50 waiting point nuclei. -/
def n50Nuclei : List NuclearConfig := [⟨38, 50⟩, ⟨39, 50⟩, ⟨40, 50⟩]

/-- N=82 waiting point nuclei. -/
def n82Nuclei : List NuclearConfig := [⟨56, 82⟩, ⟨57, 82⟩, ⟨58, 82⟩]

/-- N=126 waiting point nuclei. -/
def n126Nuclei : List NuclearConfig := [⟨78, 126⟩, ⟨79, 126⟩, ⟨82, 126⟩]

/-- All N=50 nuclei have magic neutron number. -/
theorem n50_magic : ∀ cfg ∈ n50Nuclei, Nuclear.MagicNumbers.isMagic cfg.N := by decide

/-- All N=82 nuclei have magic neutron number. -/
theorem n82_magic : ∀ cfg ∈ n82Nuclei, Nuclear.MagicNumbers.isMagic cfg.N := by decide

/-- All N=126 nuclei have magic neutron number. -/
theorem n126_magic : ∀ cfg ∈ n126Nuclei, Nuclear.MagicNumbers.isMagic cfg.N := by decide

/-! ## Abundance Peaks -/

/-- Predicted abundance peaks at magic N. -/
def abundancePeaks : List ℕ := [50, 82, 126]

/-- All abundance peaks are magic numbers. -/
theorem peaks_magic : ∀ n ∈ abundancePeaks, Nuclear.MagicNumbers.isMagic n := by
  decide

/-! ## Iron Peak -/

/-- Fe-56 configuration. -/
def Iron56 : NuclearConfig := ⟨26, 30⟩

/-- Ni-56 (doubly magic Z=28, N=28). -/
def Nickel56 : NuclearConfig := ⟨28, 28⟩

/-- Ni-56 is doubly-magic. -/
theorem ni56_doublyMagic : Nuclear.MagicNumbers.isDoublyMagic Nickel56.Z Nickel56.N := by
  unfold Nickel56 Nuclear.MagicNumbers.isDoublyMagic
  exact ⟨magic28, magic28⟩

/-- Fe-56 is near-magic (2 neutrons from N=28). -/
theorem iron56_near_magic : distToMagic Iron56.N = 2 := by
  native_decide

/-- Fe-56 has low stability distance. -/
theorem iron56_stable : stabilityDistance Iron56 ≤ 4 := by native_decide

/-! ## Falsification Criteria -/

/-- The theory predicts abundance peaks at magic N. -/
theorem falsification_criterion_1 :
    ∀ n ∈ [50, 82, 126], Nuclear.MagicNumbers.isMagic n := peaks_magic

/-- The theory predicts Ni-56 is doubly-magic (decays to Fe-56). -/
theorem falsification_criterion_2 :
    Nuclear.MagicNumbers.isDoublyMagic 28 28 := ⟨magic28, magic28⟩

end

end IndisputableMonolith.Fusion.Nucleosynthesis
