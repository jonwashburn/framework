import YMFramework

/-!
# Minimal YM-only executable
-/

def main : IO Unit := do
  IO.println "Yang–Mills: minimal scaffold"
  -- TODO: add YM-specific CLI or checks here
  pure ()
