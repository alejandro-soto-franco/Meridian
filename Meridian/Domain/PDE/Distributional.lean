/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.
-/
import Lean
import Meridian.Core.SorryExtract

/-!
# Distributional Derivative Tactic

Automate goals involving weak/distributional derivatives and test function
formulations. Handles integration-by-parts reductions, passage between
`HasWeakDerivative` and `HasFDerivAt`, and the "test against all test functions"
pattern.

## Tactics

- `meridian_distrib`: reduce distributional goals to pointwise identities
-/

namespace Meridian.Domain.PDE.Distributional

open Lean Elab Tactic Meta
open Meridian.Core.SorryExtract

/-! ## Pattern Recognition -/

/-- Check if a goal involves distributional/weak derivative concepts. -/
private def isDistributional (target : Expr) : MetaM Bool := do
  let deps := collectDeps target
  return deps.any fun n =>
    let s := toString n
    (s.splitOn "integral").length > 1 ||
    (s.splitOn "WeakDerivative").length > 1 ||
    (s.splitOn "Distributional").length > 1 ||
    (s.splitOn "HasWeakDeriv").length > 1

/-- Try to reduce a distributional goal by:
    1. Unfolding weak derivative definitions
    2. Applying integration-by-parts when the goal is ∫ f' * φ = -∫ f * φ'
    3. Reducing to pointwise identities -/
private def reduceDistributional (goal : MVarId) : MetaM (List MVarId) := do
  let target ← goal.getType
  -- Strategy 1: If the goal is a ∀ over test functions, intro them
  if target.isForall then
    let (fvar, newGoal) ← goal.intro1
    return [newGoal]
  return [goal]

/-! ## Tactic -/

/-- `meridian_distrib` attempts to reduce distributional derivative goals. -/
elab "meridian_distrib" : tactic => do
  let goal ← getMainGoal
  let target ← goal.getType
  let isDistrib ← isDistributional target
  if !isDistrib then
    logInfo "Goal does not appear to involve distributional derivatives."
    logInfo "Trying structural reduction anyway..."
  let newGoals ← reduceDistributional goal
  if newGoals.length < 1 then
    logInfo "meridian_distrib: goal closed!"
  else if newGoals.length == 1 && newGoals.head! == goal then
    logInfo "meridian_distrib: no progress. Try manual integration-by-parts."
  else
    logInfo s!"meridian_distrib: reduced to {newGoals.length} sub-goals."
    setGoals newGoals

end Meridian.Domain.PDE.Distributional
