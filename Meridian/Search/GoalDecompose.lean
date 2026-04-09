/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.
-/
import Lean

/-!
# Goal Decomposition

Break complex goals into sub-lemmas using three strategies: logical structure,
mathematical pattern recognition, and backward chaining.

## Tactics

- `meridian_decompose`: decompose the current goal into sub-lemma stubs
-/

namespace Meridian.Search.GoalDecompose

open Lean Elab Tactic Meta

/-! ## Decomposition Strategies -/

/-- A sub-lemma produced by decomposition. -/
structure SubLemma where
  name      : String
  type      : String     -- pretty-printed goal
  strategy  : String     -- which strategy produced it
  deriving Inhabited, Repr

instance : ToString SubLemma where
  toString s := s!"  lemma {s.name} : {s.type} := sorry  -- via {s.strategy}"

/-- Decompose via logical structure: And, Iff, Exists, Forall. -/
private def decomposeLogical (goal : MVarId) : MetaM (List SubLemma) := do
  let target ← goal.getType
  let target ← whnf target
  let mut results : List SubLemma := []
  -- And: P ∧ Q → two sub-goals
  if target.isAppOfArity ``And 2 then
    let p ← ppExpr target.appFn!.appArg!
    let q ← ppExpr target.appArg!
    results := results ++ [
      { name := "left", type := toString p, strategy := "And.intro left" },
      { name := "right", type := toString q, strategy := "And.intro right" }]
  -- Iff: P ↔ Q → two directions
  if target.isAppOfArity ``Iff 2 then
    let p ← ppExpr target.appFn!.appArg!
    let q ← ppExpr target.appArg!
    results := results ++ [
      { name := "mp", type := s!"{p} → {q}", strategy := "Iff.intro forward" },
      { name := "mpr", type := s!"{q} → {p}", strategy := "Iff.intro backward" }]
  -- Exists: ∃ x, P x → need witness + proof
  if target.isAppOfArity ``Exists 2 then
    let body ← ppExpr target.appArg!
    results := results ++ [
      { name := "witness", type := "provide the witness value", strategy := "Exists.intro" },
      { name := "property", type := toString body, strategy := "Exists.intro" }]
  -- Forall
  if target.isForall then
    let bodyType ← forallTelescopeReducing target fun args body => do
      let bPP ← ppExpr body
      return toString bPP
    results := results ++ [
      { name := "body", type := bodyType, strategy := "intro + prove body" }]
  return results

/-- Decompose via backward chaining: find lemmas whose conclusion matches
    and report their hypotheses as sub-goals. -/
private def decomposeBackward (goal : MVarId) : MetaM (List SubLemma) := do
  -- Simple version: check if goal is an application and suggest
  -- applying the head constant
  let target ← goal.getType
  let fn := target.getAppFn
  if fn.isConst then
    let name := fn.constName!
    let fmt ← ppExpr target
    return [{ name := s!"apply_{name}", type := toString fmt, strategy := s!"apply {name}" }]
  return []

/-! ## Main Decomposition -/

/-- Decompose a goal into sub-lemma stubs. -/
def decomposeGoal (goal : MVarId) : MetaM (List SubLemma) := do
  let mut all : List SubLemma := []
  all := all ++ (← decomposeLogical goal)
  all := all ++ (← decomposeBackward goal)
  return all

/-! ## Tactic -/

/-- `meridian_decompose` decomposes the current goal into sub-lemma stubs. -/
elab "meridian_decompose" : tactic => do
  let goal ← getMainGoal
  let subs ← decomposeGoal goal
  if subs.isEmpty then
    logInfo "No decomposition found for current goal."
  else
    let header := s!"Decomposition ({subs.length} sub-lemmas):"
    let body := "\n".intercalate (subs.map toString)
    logInfo s!"{header}\n{body}"

end Meridian.Search.GoalDecompose
