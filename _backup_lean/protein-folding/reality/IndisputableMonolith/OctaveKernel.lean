import IndisputableMonolith.OctaveKernel.Basic
import IndisputableMonolith.OctaveKernel.Invariance
import IndisputableMonolith.OctaveKernel.Adapters
import IndisputableMonolith.OctaveKernel.Instances
import IndisputableMonolith.OctaveKernel.Bridges
import IndisputableMonolith.OctaveKernel.EmpiricalAnchors
import IndisputableMonolith.OctaveKernel.IntegrationTests

/-!
# IndisputableMonolith.OctaveKernel

Umbrella import for the "Octave System" kernel.

This is intended to become the shared abstraction layer for cross-domain
octave-style reasoning (layers, channels, and bridges), without colliding with
existing domain modules like `IndisputableMonolith.Nuclear.Octave`.

## Submodules

- **Basic**: Core `Layer` and `Channel` structures
- **Invariance**: Cross-layer invariance properties
- **Adapters**: Bridges to existing Monolith modules
- **Instances**: Concrete layer witnesses (PatternCover, LNAL, Biology, Water, Consciousness, Physics)
- **Bridges**: Typed maps between layers with phase/cost preservation
- **EmpiricalAnchors**: Preregistration structures for experimental validation
- **IntegrationTests**: Cross-domain theorems connecting 3+ layers
-/
