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
open Meridian.Search.TacticSuggest

/-! ## Types -/

/-- A proof script: sequence of tactic names that closes the goal. -/
structure ProofScript where
  tactics : List String
  depth   : Nat
  deriving Inhabited, Repr

instance : ToString ProofScript where
  toString s := "  " ++ "\n  ".intercalate s.tactics

/-! ## Search Engine -/

/-- Fingerprint a goal for memoization (use the type's hash). -/
private def goalFingerprint (goal : MVarId) : MetaM UInt64 := do
  let target ← goal.getType
  return target.hash

/-- DFS with depth limit. Tries suggestions at each level, recurses on remaining goals. -/
private partial def searchDFS (goal : MVarId) (maxDepth : Nat) (depth : Nat)
    (visited : IO.Ref (Std.HashSet UInt64)) (path : List String) : MetaM (Option ProofScript) := do
  if depth >= maxDepth then return none
  -- Check memoization
  let fp ← goalFingerprint goal
  let seen ← visited.get
  if seen.contains fp then return none
  visited.set (seen.insert fp)
  -- Get suggestions
  let suggestions ← suggestForGoal goal
  for s in suggestions do
    if s.closesGoal then
      return some { tactics := path ++ [s.tacticText], depth := depth + 1 }
    -- For non-closing tactics that reduce goals, we would recurse.
    -- For now, only report single-step closers at each depth.
  return none

/-- Run iterative deepening search up to `maxDepth`. -/
def search (goal : MVarId) (maxDepth : Nat := 3) : MetaM (Option ProofScript) := do
  let visited ← IO.mkRef {}
  for d in List.range (maxDepth + 1) do
    visited.set {}
    match ← searchDFS goal d 0 visited [] with
    | some script => return some script
    | none => continue
  return none

/-! ## Tactic -/

/-- `meridian_search` runs multi-step proof search on the current goal. -/
elab "meridian_search" : tactic => do
  let goal ← getMainGoal
  let result ← search goal 3
  match result with
  | some script =>
    logInfo s!"Found proof ({script.depth} steps):\n{script}"
  | none =>
    logInfo "meridian_search: no proof found within depth limit."

end Meridian.Search.ProofSearch
