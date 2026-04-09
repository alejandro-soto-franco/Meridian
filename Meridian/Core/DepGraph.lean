/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.
-/
import Meridian.Core.SorryExtract

/-!
# Dependency Graph

Build a directed graph of declaration dependencies. Edges: `A -> B` means `A` uses
`B` in its proof or type. Annotates each node with sorry count, proven/sorry status,
and Mathlib coverage.

## Commands

- `#dep_graph`: output structured `DepGraph` + DOT format for Graphviz
-/

namespace Meridian.Core.DepGraph

open Lean Elab Command Meta
open Meridian.Core.SorryExtract

/-! ## Types -/

structure DepNode where
  name          : Name
  hasSorry      : Bool
  sorryCount    : Nat
  worstCategory : CoverageCategory
  coverages     : List CoverageResult
  deriving Inhabited, Repr

structure DepGraph where
  nodes : NameMap DepNode       := {}
  edges : NameMap (List Name)   := {}
  deriving Inhabited

/-! ## Graph Construction -/

/-- Compute the worst (highest-index) category across a list of CoverageResults.
    C > B > A, so C is worst. -/
def worstCategoryOf (covs : List CoverageResult) : CoverageCategory :=
  covs.foldl (fun acc c =>
    match acc, c.category with
    | .C, _ => .C | _, .C => .C
    | .B, _ => .B | _, .B => .B
    | _, _  => .A) .A

/-- Build a dependency graph from a list of `MeridianDecl`s.
    Only edges to other project-local declarations are included. -/
def buildDepGraph (decls : List MeridianDecl) : DepGraph := Id.run do
  let nameSet : NameSet := decls.foldl (fun acc d => acc.insert d.name) {}
  let mut nodes : NameMap DepNode := {}
  let mut edges : NameMap (List Name) := {}
  for d in decls do
    let node : DepNode := {
      name := d.name
      hasSorry := d.hasSorry
      sorryCount := d.sorryGoals.length
      worstCategory := if d.hasSorry then worstCategoryOf d.coverages else .A
      coverages := d.coverages
    }
    nodes := nodes.insert d.name node
    let localDeps := d.deps.filter nameSet.contains
    edges := edges.insert d.name localDeps
  return { nodes, edges }

/-! ## Graph Analysis -/

/-- Count how many declarations transitively depend on `target`
    (downstream impact: how many nodes reach `target`). -/
private partial def bfs (rev : NameMap (List Name)) (queue : List Name) (visited : NameSet) : Nat :=
  match queue with
  | [] => visited.size
  | n :: rest =>
    if visited.contains n then bfs rev rest visited
    else
      let visited' := visited.insert n
      let neighbours := (rev.find? n).getD []
      bfs rev (rest ++ neighbours) visited'

def transitiveDepCount (g : DepGraph) (target : Name) : Nat := Id.run do
  -- Build reverse graph
  let mut rev : NameMap (List Name) := {}
  for (src, dsts) in g.edges.toList do
    for dst in dsts do
      let existing := (rev.find? dst).getD []
      rev := rev.insert dst (src :: existing)
  return bfs rev [target] {}

/-- DFS with fuel to find the longest sorry chain from a node. -/
private def dfs (g : DepGraph) (sorryNames : NameSet) (n : Name) (visited : NameSet)
    (fuel : Nat) : List Name :=
  match fuel with
  | 0 => [n]
  | fuel' + 1 =>
    if visited.contains n then []
    else
      let visited' := visited.insert n
      let children := ((g.edges.find? n).getD []).filter sorryNames.contains
      let childChains := children.map (fun c => dfs g sorryNames c visited' fuel')
      let longestChild := childChains.foldl
        (fun acc c => if c.length > acc.length then c else acc) []
      n :: longestChild

def longestSorryChain (g : DepGraph) : List Name := Id.run do
  let sorryNames : NameSet := g.nodes.toList.foldl (fun acc (n, node) =>
    if node.hasSorry then acc.insert n else acc) {}
  let fuel := g.nodes.toList.length
  let mut best : List Name := []
  for (name, _) in g.nodes.toList do
    if !sorryNames.contains name then continue
    let chain := dfs g sorryNames name {} fuel
    if chain.length > best.length then
      best := chain
  return best

/-! ## Output Formatting -/

/-- Render the graph as a Graphviz DOT string. -/
def toDOT (g : DepGraph) : String := Id.run do
  let mut lines : List String := [
    "digraph MeridianDeps {",
    "  rankdir=BT;",
    "  node [shape=box, style=filled, fontname=\"monospace\"];"]
  for (name, node) in g.nodes.toList do
    let colour := if !node.hasSorry then "\"#90EE90\""
      else match node.worstCategory with
        | .A => "\"#FFFF99\""
        | .B => "\"#FFD699\""
        | .C => "\"#FF9999\""
    let label := s!"{name}\\nsorries: {node.sorryCount}"
    lines := lines ++ [s!"  \"{name}\" [label=\"{label}\", fillcolor={colour}];"]
  for (src, dsts) in g.edges.toList do
    for dst in dsts do
      lines := lines ++ [s!"  \"{src}\" -> \"{dst}\";"]
  lines := lines ++ ["}"]
  return "\n".intercalate lines

/-- Render a human-readable text summary. -/
def toSummary (g : DepGraph) : String :=
  let nodeCount := g.nodes.toList.length
  let edgeCount := g.edges.toList.foldl (fun acc (_, es) => acc + es.length) 0
  let sorryNodes := g.nodes.toList.filter (·.2.hasSorry)
  let catA := sorryNodes.filter (·.2.worstCategory == .A) |>.length
  let catB := sorryNodes.filter (·.2.worstCategory == .B) |>.length
  let catC := sorryNodes.filter (·.2.worstCategory == .C) |>.length
  let critPath := longestSorryChain g
  let critNames := ", ".intercalate (critPath.map toString)
  s!"Nodes: {nodeCount}, Edges: {edgeCount}\n" ++
  s!"Sorry nodes: {sorryNodes.length} (A={catA}, B={catB}, C={catC})\n" ++
  s!"Critical sorry chain ({critPath.length}): {critNames}"

/-! ## Commands -/

elab "#dep_graph" : command => do
  let decls ← extractAllDecls
  let graph := buildDepGraph decls
  logInfo (toDOT graph)
  logInfo (toSummary graph)

end Meridian.Core.DepGraph
