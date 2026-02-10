-- RecogSpec: Recognition Science Specification Layer
-- Moved from RH/RS to provide a cleaner module name

import IndisputableMonolith.RecogSpec.Core
import IndisputableMonolith.RecogSpec.Anchors
import IndisputableMonolith.RecogSpec.Bands
import IndisputableMonolith.RecogSpec.Scales
import IndisputableMonolith.RecogSpec.PhiSelectionCore
import IndisputableMonolith.RecogSpec.Spec
import IndisputableMonolith.RecogSpec.Framework
import IndisputableMonolith.RecogSpec.InevitabilityScaffold
import IndisputableMonolith.RecogSpec.ClosureShim
import IndisputableMonolith.RecogSpec.MatchesLegacy
import IndisputableMonolith.RecogSpec.DimlessEvaluator
import IndisputableMonolith.RecogSpec.UDExplicit
import IndisputableMonolith.RecogSpec.Universe
import IndisputableMonolith.RecogSpec.Witness
import IndisputableMonolith.RecogSpec.RSLedger
import IndisputableMonolith.RecogSpec.RSBridge
import IndisputableMonolith.RecogSpec.RSCompliance

/-!
# RecogSpec - Recognition Science Specification

This module provides the specification layer for Recognition Science,
including:

* Core ledger and bridge structures
* φ-closure and universal dimensionless packs
* Calibration, bands, and measurement anchors
* Inevitability and recognition closure predicates
* Rich ledger/bridge structures for structure-derived evaluators

## History

This module was previously located at `RH/RS/` but has been moved to
`RecogSpec/` to provide a clearer module name that reflects its purpose
(Recognition Science Specification) rather than an earlier project context.
-/
