/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.
-/
import Meridian.Analysis.MathlibCoverage
import Meridian.Core.DepGraph

/-!
# Gap Report

Aggregate `MathlibCoverage` across all sorries in the project. Group by missing
infrastructure, rank by `(downstream impact) * (Mathlib closeness)`, output
structured report + Markdown.

## Commands

- `#gap_report`: project-level Mathlib gap analysis
-/

namespace Meridian.Analysis.GapReport

open Lean Elab Command Meta
open Meridian.Core.SorryExtract
open Meridian.Core.DepGraph
open Meridian.Analysis.MathlibCoverage

/-! ## Types -/

/-- A gap group: a collection of sorries that share the same missing infrastructure. -/
structure GapGroup where
  gapKind       : GapKind
  description   : String
  affectedDecls : List Name
  totalImpact   : Nat       -- sum of downstream impacts
  deriving Inhabited, Repr

/-! ## Report Generation -/

/-- Build a gap report across all sorry-containing declarations. -/
def buildGapReport (decls : List MeridianDecl) (graph : DepGraph) :
    MetaM (List GapGroup) := do
  let tree ← buildMathlibDiscrTree
  let sorryDecls := decls.filter (·.hasSorry)
  -- Collect all classified near-misses per sorry
  let mut kindMap : Std.HashMap String (GapKind × List Name × Nat) := {}
  for d in sorryDecls do
    let impact := transitiveDepCount graph d.name
    for goal in d.sorryGoals do
      let (_, classified) ← deepCoverage tree goal
      if classified.isEmpty then
        -- Category C: no near-misses at all
        let key := "no_mathlib_coverage"
        let (kind, names, imp) := (kindMap.getD key (.infrastructure, [], 0))
        kindMap := kindMap.insert key (kind, names ++ [d.name], imp + impact)
      else
        for c in classified do
          let key := toString c.gapKind
          let (kind, names, imp) := (kindMap.getD key (c.gapKind, [], 0))
          kindMap := kindMap.insert key (kind, names ++ [d.name], imp + impact)
  -- Convert to GapGroups
  let mut groups : List GapGroup := []
  for (desc, (kind, names, impact)) in kindMap.toList do
    -- Deduplicate names
    let uniqueNames := names.eraseDups
    groups := groups ++ [{
      gapKind := kind
      description := desc
      affectedDecls := uniqueNames
      totalImpact := impact
    }]
  -- Sort by total impact descending
  return groups.mergeSort (fun a b => a.totalImpact > b.totalImpact)

/-! ## Commands -/

/-- `#gap_report` produces a project-level Mathlib gap analysis. -/
elab "#gap_report" : command => do
  let decls ← extractAllDecls
  let graph := buildDepGraph decls
  let groups ← liftTermElabM <| buildGapReport decls graph
  if groups.isEmpty then
    logInfo "No gaps found (no sorries in the project)."
    return
  let mut msg := s!"Gap Report ({groups.length} gap categories)\n" ++
    String.ofList (List.replicate 60 '=') ++ "\n"
  for (g, i) in groups.zip (List.range groups.length) do
    msg := msg ++ s!"\n{i + 1}. [{g.gapKind}] {g.description}\n"
    msg := msg ++ s!"   Affected: {g.affectedDecls.length} declarations, "
    msg := msg ++ s!"Total downstream impact: {g.totalImpact}\n"
    for name in g.affectedDecls.take 10 do
      msg := msg ++ s!"   - {name}\n"
    if g.affectedDecls.length > 10 then
      msg := msg ++ s!"   ... and {g.affectedDecls.length - 10} more\n"
  logInfo msg

/-- `#gap_report_all` runs gap analysis across all imported user modules.

    Mirrors `#sorry_inventory_all`: useful when invoking from a scratch buffer
    or any file that doesn't itself contain the sorries you want to analyse. -/
elab "#gap_report_all" : command => do
  let decls ← extractAllUserDeclsWithCoverage
  let graph := buildDepGraph decls
  let groups ← liftTermElabM <| buildGapReport decls graph
  if groups.isEmpty then
    logInfo "No gaps found (no sorries in any imported user module)."
    return
  let mut msg := s!"Gap Report ({groups.length} gap categories)\n" ++
    String.ofList (List.replicate 60 '=') ++ "\n"
  for (g, i) in groups.zip (List.range groups.length) do
    msg := msg ++ s!"\n{i + 1}. [{g.gapKind}] {g.description}\n"
    msg := msg ++ s!"   Affected: {g.affectedDecls.length} declarations, "
    msg := msg ++ s!"Total downstream impact: {g.totalImpact}\n"
    for name in g.affectedDecls.take 10 do
      msg := msg ++ s!"   - {name}\n"
    if g.affectedDecls.length > 10 then
      msg := msg ++ s!"   ... and {g.affectedDecls.length - 10} more\n"
  logInfo msg

end Meridian.Analysis.GapReport
