/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.
-/
import Lean

/-!
# Tactic Suggestion

Given a goal state, run candidate tactics in isolated `Meta.State` snapshots and
rank results. Uses `DiscrTree` for head symbol lookup, one-shot closers, parametric
tactics, and rewrite candidates.

## Tactics

- `meridian_suggest`: suggest and rank tactics for the current goal

## Commands

- `#meridian_suggest declName`: suggest tactics for a specific sorry
-/

namespace Meridian.Search.TacticSuggest

open Lean Elab Tactic Meta

end Meridian.Search.TacticSuggest
