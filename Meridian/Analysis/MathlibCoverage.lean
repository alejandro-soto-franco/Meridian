/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.
-/
import Meridian.Core.SorryExtract

/-!
# Mathlib Coverage Analysis

Given a goal, find "close" Mathlib lemmas by querying the `DiscrTree` with up to N
mismatches. Classify each near-miss: specialisation gap, exponent gap, dimensionality
gap, or missing infrastructure.

## Commands

- `#mathlib_coverage declName`: find near-miss Mathlib lemmas for a sorry

## Tactics

- `meridian_coverage`: print coverage results in the infoview
-/

namespace Meridian.Analysis.MathlibCoverage

open Lean Elab Command Tactic Meta
open Meridian.Core.SorryExtract

/-! ## Gap Classification -/

/-- Classify the type of gap between a sorry goal and a near-miss. -/
inductive GapKind where
  | specialisation   -- Mathlib has a more general version
  | exponent         -- wrong Lp exponent or Sobolev index
  | dimensionality   -- wrong dimension (R^n vs R^m)
  | infrastructure   -- missing foundational definition
  | unknown
  deriving Inhabited, BEq, Repr

instance : ToString GapKind where
  toString
    | .specialisation  => "specialisation"
    | .exponent        => "exponent"
    | .dimensionality  => "dimensionality"
    | .infrastructure  => "infrastructure"
    | .unknown         => "unknown"

/-- A classified near-miss with gap analysis. -/
structure ClassifiedNearMiss where
  nearMiss  : NearMiss
  gapKind   : GapKind
  gapDetail : String
  deriving Inhabited, Repr

/-- Heuristically classify a near-miss gap based on mismatch descriptions. -/
private def classifyGap (nm : NearMiss) : GapKind :=
  let descs := nm.mismatchDescriptions
  -- Check for dimension-related mismatches
  if descs.any (fun d => (d.splitOn "Fin").length > 1 || (d.splitOn "EuclideanSpace").length > 1) then
    .dimensionality
  -- Check for exponent mismatches (ENNReal, NNReal, p, q)
  else if descs.any (fun d => (d.splitOn "ENNReal").length > 1 || (d.splitOn "NNReal").length > 1) then
    .exponent
  -- If only 1 mismatch, likely a specialisation
  else if nm.mismatchCount == 1 then
    .specialisation
  else
    .unknown

/-- Run deep coverage analysis for a single sorry goal. -/
def deepCoverage (tree : DiscrTree Name) (goal : Expr) : MetaM (CoverageResult × List ClassifiedNearMiss) := do
  let cov ← queryCoverage tree goal
  let classified := cov.nearMisses.map fun nm =>
    let kind := classifyGap nm
    let detail := ", ".intercalate nm.mismatchDescriptions
    { nearMiss := nm, gapKind := kind, gapDetail := detail }
  return (cov, classified)

/-! ## Commands -/

/-- `#mathlib_coverage declName` finds near-miss Mathlib lemmas for a sorry. -/
elab "#mathlib_coverage" declName:ident : command => do
  let name := declName.getId
  let env ← getEnv
  match env.find? name with
  | none => throwError "Declaration '{name}' not found"
  | some ci =>
    let (cov, classified) ← liftTermElabM do
      let tree ← buildMathlibDiscrTree
      -- Get the sorry goals
      let goals := match ci.value? with
        | some v => collectSorryGoals v
        | none => [ci.type]  -- If no value, use the type itself
      if goals.isEmpty then
        deepCoverage tree ci.type
      else
        deepCoverage tree goals.head!
    let mut msg := s!"Coverage for {name}: Category {cov.category}\n"
    if !cov.exactMatches.isEmpty then
      msg := msg ++ s!"Exact matches ({cov.exactMatches.length}):\n"
      for m in cov.exactMatches.take 10 do
        msg := msg ++ s!"  - {m}\n"
    if !classified.isEmpty then
      msg := msg ++ s!"Near-misses ({classified.length}):\n"
      for c in classified.take 15 do
        msg := msg ++ s!"  [{c.gapKind}] {c.nearMiss.name} ({c.nearMiss.mismatchCount} mismatches)\n"
        msg := msg ++ s!"    {c.gapDetail}\n"
    if cov.exactMatches.isEmpty && classified.isEmpty then
      msg := msg ++ "No matches or near-misses found in Mathlib."
    logInfo msg

/-! ## Tactic -/

/-- `meridian_coverage` prints coverage results for the current goal. -/
elab "meridian_coverage" : tactic => do
  let goal ← getMainGoal
  let target ← goal.getType
  let tree ← buildMathlibDiscrTree
  let (cov, classified) ← deepCoverage tree target
  let mut msg := s!"Coverage: Category {cov.category}\n"
  for m in cov.exactMatches.take 5 do
    msg := msg ++ s!"  exact: {m}\n"
  for c in classified.take 10 do
    msg := msg ++ s!"  [{c.gapKind}] {c.nearMiss.name} ({c.nearMiss.mismatchCount} mismatches)\n"
  logInfo msg

end Meridian.Analysis.MathlibCoverage
