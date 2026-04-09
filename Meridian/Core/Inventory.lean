/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.
-/
import Meridian.Core.SorryExtract
import Meridian.Core.DepGraph

/-!
# Sorry Inventory

Produce a table of all sorries in the project: file, declaration name, goal type,
and estimated category (A/B/C based on Mathlib reachability).

## Commands

- `#sorry_inventory`: tabular sorry report with auto-categorisation
-/

namespace Meridian.Core.Inventory

open Lean Elab Command Meta
open Meridian.Core.SorryExtract
open Meridian.Core.DepGraph

structure InventoryEntry where
  decl             : MeridianDecl
  downstreamImpact : Nat
  priority         : Float
  deriving Inhabited

/-- Compute the worst category across all coverages of a declaration. -/
private def worstCategory (d : MeridianDecl) : CoverageCategory :=
  worstCategoryOf d.coverages

/-- Weight for priority scoring. -/
private def closenessWeight : CoverageCategory → Float
  | .A => 3.0
  | .B => 2.0
  | .C => 1.0

/-- Build the inventory: sorry-containing decls with priority scores. -/
def buildInventory (decls : List MeridianDecl) (graph : DepGraph) : List InventoryEntry := Id.run do
  let sorryDecls := decls.filter (·.hasSorry)
  let mut entries : List InventoryEntry := []
  for d in sorryDecls do
    let impact := transitiveDepCount graph d.name
    let prio := (Float.ofNat (impact + 1)) * closenessWeight (worstCategory d)
    entries := entries ++ [{ decl := d, downstreamImpact := impact, priority := prio }]
  return entries.mergeSort (fun a b => a.priority > b.priority)

/-- Format an inventory entry as a table row. -/
private def formatEntry (rank : Nat) (e : InventoryEntry) : MetaM String := do
  let sig ← ppExpr e.decl.type
  let sigStr := toString sig
  let truncSig := if sigStr.length > 60 then (sigStr.take 57).toString ++ "..." else sigStr
  let cat := worstCategory e.decl
  let nearMissCount := e.decl.coverages.foldl (fun acc c => acc + c.nearMisses.length) 0
  return s!"  {rank}. [{cat}] {e.decl.name}\n" ++
    s!"     Goal: {truncSig}\n" ++
    s!"     Near-misses: {nearMissCount}, Downstream: {e.downstreamImpact}, " ++
    s!"Priority: {e.priority}"

/-! ## Commands -/

elab "#sorry_inventory" : command => do
  let decls ← extractAllDecls
  let graph := buildDepGraph decls
  let entries := buildInventory decls graph
  if entries.isEmpty then
    logInfo "No sorries found."
    return
  let header := s!"Sorry Inventory ({entries.length} sorries)\n" ++
    String.ofList (List.replicate 60 '=') ++ "\n"
  let mut msg := header
  for (e, i) in entries.zip (List.range entries.length) do
    let row ← liftTermElabM <| formatEntry (i + 1) e
    msg := msg ++ row ++ "\n"
  logInfo msg

end Meridian.Core.Inventory
