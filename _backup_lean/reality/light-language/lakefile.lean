import Lake
open Lake DSL

package «lightlanguage» where
  version := v!"0.1.0"
  keywords := #["recognition-science", "consciousness", "formal-verification"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «LightLanguage» where
  roots := #[`LightLanguage]

lean_exe «lightlanguage» where
  root := `Main
  supportInterpreter := true
