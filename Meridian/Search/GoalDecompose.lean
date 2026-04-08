/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.
-/
import Lean

/-!
# Goal Decomposition

Break complex goals into sub-lemmas using three strategies: logical structure,
mathematical pattern recognition, and backward chaining. Extensible via
`@[meridian_pattern]` attribute.

## Tactics

- `meridian_decompose`: decompose the current goal into sub-lemma stubs
-/

namespace Meridian.Search.GoalDecompose

open Lean Elab Tactic Meta

end Meridian.Search.GoalDecompose
