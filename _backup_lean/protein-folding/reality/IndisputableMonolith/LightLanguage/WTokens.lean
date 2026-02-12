import IndisputableMonolith.Water.WTokenIso

/-!
# `IndisputableMonolith.LightLanguage.WTokens` (compatibility layer)

The canonical spec (`Source-Super-rrf.txt`) talks about a “LightLanguage / ULL”
layer with WTokens (semantic atoms).

In this repo snapshot, the implemented WToken development lives under the Water
namespace (`IndisputableMonolith.Water.WTokenIso`). This module provides
lightweight aliases to reduce naming drift without duplicating definitions.
-/

namespace IndisputableMonolith.LightLanguage

abbrev WTokenMode := IndisputableMonolith.Water.WTokenMode
abbrev PhiLevel := IndisputableMonolith.Water.PhiLevel
abbrev TauOffset := IndisputableMonolith.Water.TauOffset

abbrev WTokenSpec := IndisputableMonolith.Water.WTokenSpec
abbrev WToken := IndisputableMonolith.Water.WToken

abbrev AminoAcid := IndisputableMonolith.Water.AminoAcid

abbrev allWTokens := IndisputableMonolith.Water.allWTokens

abbrev wtoken_to_amino := IndisputableMonolith.Water.wtoken_to_amino
abbrev amino_to_wtoken := IndisputableMonolith.Water.amino_to_wtoken

abbrev wtoken_amino_bijection := IndisputableMonolith.Water.wtoken_amino_bijection
abbrev wtoken_amino_equiv := IndisputableMonolith.Water.wtoken_amino_equiv

end IndisputableMonolith.LightLanguage
