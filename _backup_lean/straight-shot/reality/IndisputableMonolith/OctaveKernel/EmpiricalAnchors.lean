import IndisputableMonolith.OctaveKernel.EmpiricalAnchors.NeuralPhiBands
import IndisputableMonolith.OctaveKernel.EmpiricalAnchors.TauGateProtocol

/-!
# IndisputableMonolith.OctaveKernel.EmpiricalAnchors

Umbrella imports for empirical anchor modules that define preregistration structures,
hypotheses, and falsifier hooks for experimental validation of the Octave System.

## Available Modules

- **NeuralPhiBands**: EEG φ-band scaling hypothesis and semantic category mapping
- **TauGateProtocol**: Tau-gate (~65 ps) measurement protocol and IR band structure

## Claim hygiene

All empirical claims in these modules are:
1. Explicitly marked as `Hypothesis` or `EmpiricalAnchor`
2. Associated with falsifier predicates
3. Structured for preregistration (dataset requirements, thresholds defined upfront)

These are **not** theorems about nature — they are formal interfaces for
empirical testing.
-/
