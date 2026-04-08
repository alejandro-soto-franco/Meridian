/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.
-/
import Meridian.Search.TacticSuggest

/-!
# Proof Search

Iterative deepening A* (IDA*) over tactic sequences. Uses `TacticSuggest` for
candidate generation, goal fingerprinting for memoization, and heartbeat-based
timeout for reproducibility.

## Tactics

- `meridian_search (heartbeats := 400000)`: multi-step proof search
-/

namespace Meridian.Search.ProofSearch

open Lean Elab Tactic Meta

end Meridian.Search.ProofSearch
