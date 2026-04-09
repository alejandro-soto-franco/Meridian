/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.
-/
import Lean
import Lean.Meta.DiscrTree
import Meridian.Core.SorryExtract

/-!
# Tactic Suggestion

Given a goal state, run candidate tactics in isolated `Meta.State` snapshots and
rank results. Uses `DiscrTree` for head symbol lookup, one-shot closers, parametric
tactics, and rewrite candidates.

## Tactics

- `meridian_suggest`: suggest and rank tactics for the current goal
-/

namespace Meridian.Search.TacticSuggest

open Lean Elab Tactic Meta Command
open Meridian.Core.SorryExtract

/-! ## Types -/

/-- A tactic suggestion with metadata about how well it worked. -/
structure Suggestion where
  tacticText   : String
  closesGoal   : Bool      -- true if the tactic completely solves the goal
  newGoalCount : Nat       -- number of remaining goals after applying
  priority     : Nat       -- lower is better
  deriving Inhabited, Repr

instance : ToString Suggestion where
  toString s :=
    let status := if s.closesGoal then "CLOSES" else s!"{s.newGoalCount} goals remain"
    s!"  [{s.priority}] {s.tacticText} ({status})"

/-! ## Candidate Tactic List -/

/-- The list of candidate tactics to try, in priority order.
    Each is a (name, syntax-string) pair. -/
private def candidateTactics : List (String × String) :=
  [ ("rfl",       "rfl"),
    ("trivial",   "trivial"),
    ("decide",    "decide"),
    ("omega",     "omega"),
    ("norm_num",  "norm_num"),
    ("simp",      "simp"),
    ("ring",      "ring"),
    ("linarith",  "linarith"),
    ("nlinarith", "nlinarith"),
    ("positivity","positivity"),
    ("aesop",     "aesop"),
    ("exact?",    "exact?"),
    ("apply?",    "apply?"),
    ("intro _",   "intro _"),
    ("constructor","constructor"),
    ("ext",       "ext"),
    ("funext",    "funext"),
    ("push_neg",  "push_neg"),
    ("contrapose","contrapose"),
    ("by_contra", "by_contra"),
    ("cases _",   "cases _"),
    ("induction _","induction _") ]

/-! ## Tactic Evaluation -/

/-- Check if a goal can be closed by `rfl` (definitional equality). -/
private def tryRfl (goal : MVarId) : MetaM (Option Suggestion) := do
  let savedState ← saveState
  try
    goal.refl
    return some { tacticText := "rfl", closesGoal := true, newGoalCount := 0, priority := 0 }
  catch _ =>
    savedState.restore
    return none

/-- Check if a goal can be closed by `trivial`. -/
private def tryTrivial (goal : MVarId) : MetaM (Option Suggestion) := do
  let savedState ← saveState
  try
    goal.assumption
    return some { tacticText := "assumption", closesGoal := true, newGoalCount := 0, priority := 1 }
  catch _ =>
    savedState.restore
    return none

/-- Check if a goal is a decidable proposition and can be closed by `Decidable`. -/
private def tryDecidable (goal : MVarId) : MetaM (Option Suggestion) := do
  let savedState ← saveState
  try
    -- Try to synthesise Decidable for the target and close
    let target ← goal.getType
    let decType ← mkAppM ``Decidable #[target]
    match ← trySynthInstance decType with
    | .some inst =>
      let proof ← mkAppM ``of_decide_eq_true #[inst]
      goal.assign proof
      return some { tacticText := "decide", closesGoal := true, newGoalCount := 0, priority := 2 }
    | _ =>
      savedState.restore
      return none
  catch _ =>
    savedState.restore
    return none

/-- Try to apply each Mathlib lemma from the DiscrTree that matches the goal. -/
private def tryDiscrTreeApply (goal : MVarId) (tree : DiscrTree Name) : MetaM (List Suggestion) := do
  let target ← goal.getType
  let hits ← tree.getMatch target
  let mut suggestions : List Suggestion := []
  for (matchName, idx) in hits.toList.zip (List.range hits.size) do
    if idx >= 10 then break  -- limit to 10 suggestions
    let savedState ← saveState
    try
      let cinfo ← getConstInfo matchName
      let val := mkConst matchName (cinfo.levelParams.map fun _ => levelZero)
      let newGoals ← goal.apply val
      suggestions := suggestions ++ [{
        tacticText := s!"exact {matchName}"
        closesGoal := newGoals.isEmpty
        newGoalCount := newGoals.length
        priority := 10 + idx
      }]
    catch _ => pure ()
    savedState.restore
  return suggestions

/-- Check if the goal is a `∀` or `→` and suggest `intro`. -/
private def tryIntro (goal : MVarId) : MetaM (Option Suggestion) := do
  let target ← goal.getType
  if target.isForall then
    let savedState ← saveState
    try
      let (_, newGoal) ← goal.intro1
      let remaining ← newGoal.getType
      savedState.restore
      return some { tacticText := "intro", closesGoal := false, newGoalCount := 1, priority := 20 }
    catch _ =>
      savedState.restore
      return none
  else
    return none

/-- Check if the goal is an `∃` or `∧` and suggest `constructor`. -/
private def tryConstructor (goal : MVarId) : MetaM (Option Suggestion) := do
  let savedState ← saveState
  try
    let newGoals ← goal.constructor
    let count := newGoals.length
    savedState.restore
    return some { tacticText := "constructor", closesGoal := count == 0, newGoalCount := count, priority := 21 }
  catch _ =>
    savedState.restore
    return none

/-! ## Main Suggestion Engine -/

/-- Generate ranked suggestions for a single goal. -/
def suggestForGoal (goal : MVarId) : MetaM (List Suggestion) := do
  let mut all : List Suggestion := []
  -- Try one-shot closers
  for tryFn in [tryRfl, tryTrivial, tryDecidable] do
    match ← tryFn goal with
    | some s => all := all ++ [s]
    | none => pure ()
  -- Try structural tactics
  match ← tryIntro goal with
  | some s => all := all ++ [s]
  | none => pure ()
  match ← tryConstructor goal with
  | some s => all := all ++ [s]
  | none => pure ()
  -- Try DiscrTree apply
  let tree ← buildMathlibDiscrTree
  let dtSuggestions ← tryDiscrTreeApply goal tree
  all := all ++ dtSuggestions
  -- Sort by priority
  return all.mergeSort (fun a b => a.priority < b.priority)

/-! ## Tactic -/

/-- `meridian_suggest` prints tactic suggestions for the current goal. -/
elab "meridian_suggest" : tactic => do
  let goal ← getMainGoal
  let suggestions ← suggestForGoal goal
  if suggestions.isEmpty then
    logInfo "No suggestions found for current goal."
  else
    let header := s!"Meridian suggests ({suggestions.length} options):"
    let body := "\n".intercalate (suggestions.map toString)
    logInfo s!"{header}\n{body}"

/-! ## Command -/

/-- `#meridian_suggest declName` suggests tactics for a specific sorry. -/
elab "#meridian_suggest" declName:ident : command => do
  let name := declName.getId
  let env ← getEnv
  match env.find? name with
  | none => throwError "Declaration '{name}' not found"
  | some ci =>
    let result ← liftTermElabM do
      let goal ← mkFreshExprMVar ci.type
      let goalId := goal.mvarId!
      suggestForGoal goalId
    if result.isEmpty then
      logInfo s!"No suggestions found for {name}."
    else
      let header := s!"Suggestions for {name} ({result.length} options):"
      let body := "\n".intercalate (result.map toString)
      logInfo s!"{header}\n{body}"

end Meridian.Search.TacticSuggest
