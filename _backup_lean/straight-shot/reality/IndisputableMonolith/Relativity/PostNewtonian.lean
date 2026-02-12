-- Post-Newtonian Module Aggregator
import IndisputableMonolith.Relativity.PostNewtonian.Metric1PN
import IndisputableMonolith.Relativity.PostNewtonian.Einstein1PN
import IndisputableMonolith.Relativity.PostNewtonian.Solutions
import IndisputableMonolith.Relativity.PostNewtonian.GammaExtraction
import IndisputableMonolith.Relativity.PostNewtonian.BetaExtraction
import IndisputableMonolith.Relativity.PostNewtonian.SolarSystemBounds

/-!
# Post-Newtonian Approximation Module

Provides 1PN (first post-Newtonian) expansion for Solar System tests:
- `Metric1PN` - 1PN metric ansatz g_μν = η_μν + h_μν^(1PN)
- `Einstein1PN` - 1PN Einstein equations expansion
- `Solutions` - U, U_2, V_i potential solutions
- `GammaExtraction` - PPN γ(α, C_lag) extraction
- `BetaExtraction` - PPN β(α, C_lag) extraction
- `SolarSystemBounds` - Cassini/LLR constraint verification
-/
