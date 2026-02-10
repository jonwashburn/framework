/-!
  Minimal CI smoke: keep this executable extremely lightweight to avoid
  heavy import cycles. The hard CI gate is the audit comparator; this
  binary simply confirms the toolchain runs.
-/

def main : IO Unit := do
  IO.println "CI smoke: toolchain OK"
