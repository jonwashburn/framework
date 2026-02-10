import Hodge.Main

/-!
# `Hodge` (Proof-Track Entry Point)

This root module is intentionally **minimal**: it imports only the proof-track entry
point `Hodge.Main`, which contains the final public statement `hodge_conjecture`.

## Siloed / Off-Track Code

Modules that are **not required** for the main proof (and may contain `sorry` or
additional Classical-Pillar axioms) are intentionally *not* imported here.

To work with those modules, import one of:
- `Hodge.OffTrack` (siloed, non-proof-track modules)
- `Hodge.All` (proof-track + off-track convenience umbrella)
-/
