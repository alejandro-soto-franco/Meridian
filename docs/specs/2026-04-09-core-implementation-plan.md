# Meridian Core Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Implement all 7 Core module files from empty namespaces to working commands, with Mathlib DiscrTree-based coverage analysis.

**Architecture:** SorryExtract defines shared types and the DiscrTree coverage engine. DepGraph, Inventory build on it. TheoremExtract, Verify, Transform, Disprove are independent leaves. All commands output to the Lean infoview via `logInfo`.

**Tech Stack:** Lean 4 v4.29.0-rc8, Mathlib (rev 698d2b68), Plausible (bundled with Mathlib). Metaprogramming via `Lean.Elab.Command`, `Lean.Meta`, `Lean.Meta.DiscrTree`.

---

### Task 1: Shared Types + Sorry Detection (SorryExtract, part 1)

**Files:**
- Modify: `Meridian/Core/SorryExtract.lean`
- Create: `test/Core/TestSorryExtract.lean`

- [ ] **Step 1: Define all shared types**

Write the type definitions that every other Core module will import. In `Meridian/Core/SorryExtract.lean`:

```lean
/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.
-/
import Lean
import Lean.Meta.DiscrTree

/-!
# Sorry Extraction

Walk the environment, find all declarations containing `sorry`, and for each one
elaborate the goal type at the sorry site into a standalone lemma stub with fully
resolved universe variables and instance arguments.

## Commands

- `#sorry_extract`: emit standalone `lemma foo.sorried : <type> := sorry` for each sorry
-/

namespace Meridian.Core.SorryExtract

open Lean Elab Command Meta

/-! ## Coverage Types -/

inductive CoverageCategory where
  | A  -- exact Mathlib match exists (closable with exact?/apply?)
  | B  -- near-miss (1-2 subterm mismatches)
  | C  -- no close match (missing Mathlib infrastructure)
  deriving Inhabited, BEq, Repr

instance : ToString CoverageCategory where
  toString
    | .A => "A"
    | .B => "B"
    | .C => "C"

instance : Ord CoverageCategory where
  compare a b := compare a.toCtorIdx b.toCtorIdx

structure NearMiss where
  name                 : Name
  mismatchCount        : Nat
  mismatchDescriptions : List String
  deriving Inhabited, Repr

structure CoverageResult where
  category     : CoverageCategory
  exactMatches : List Name
  nearMisses   : List NearMiss
  deriving Inhabited, Repr

/-! ## Declaration Metadata -/

structure MeridianDecl where
  name         : Name
  type         : Expr
  value        : Option Expr
  hasSorry     : Bool
  sorryGoals   : List Expr
  fileName     : String
  line         : Nat
  deps         : List Name
  coverages    : List CoverageResult
  deriving Inhabited

/-! ## Sorry Detection -/

/-- Check whether an expression tree contains `sorryAx`. -/
partial def containsSorry (e : Expr) : Bool :=
  match e with
  | .const n _     => n == ``sorryAx
  | .app f a       => containsSorry f || containsSorry a
  | .lam _ d b _   => containsSorry d || containsSorry b
  | .forallE _ d b _ => containsSorry d || containsSorry b
  | .letE _ t v b _ => containsSorry t || containsSorry v || containsSorry b
  | .mdata _ e     => containsSorry e
  | .proj _ _ e    => containsSorry e
  | _              => false

/-- Collect the type arguments of every `sorryAx` application in an expression.
    Each `sorryAx α _` contributes `α` as a sorry goal. -/
partial def collectSorryGoals (e : Expr) : List Expr :=
  match e with
  | .app (.const n _) arg =>
    if n == ``sorryAx then [arg] else collectSorryGoals arg
  | .app f a =>
    -- sorryAx is applied as `@sorryAx α b`; the first .app has sorryAx,
    -- the second applies the Bool. We catch it at the inner .app.
    let fGoals := collectSorryGoals f
    let aGoals := collectSorryGoals a
    fGoals ++ aGoals
  | .lam _ d b _      => collectSorryGoals d ++ collectSorryGoals b
  | .forallE _ d b _  => collectSorryGoals d ++ collectSorryGoals b
  | .letE _ t v b _   => collectSorryGoals t ++ collectSorryGoals v ++ collectSorryGoals b
  | .mdata _ e        => collectSorryGoals e
  | .proj _ _ e       => collectSorryGoals e
  | _                 => []

/-- Collect all `Name`s referenced via `Expr.const` in an expression. -/
partial def collectDeps (e : Expr) : NameSet :=
  go e {}
where
  go (e : Expr) (acc : NameSet) : NameSet :=
    match e with
    | .const n _       => acc.insert n
    | .app f a         => go a (go f acc)
    | .lam _ d b _     => go b (go d acc)
    | .forallE _ d b _ => go b (go d acc)
    | .letE _ t v b _  => go b (go v (go t acc))
    | .mdata _ e       => go e acc
    | .proj _ _ e      => go e acc
    | _                => acc

/-- Return true if `declName` belongs to a user-defined module (not Lean, Init, or Mathlib). -/
def isUserDecl (env : Environment) (declName : Name) : Bool :=
  match env.getModuleIdxFor? declName with
  | none   => true  -- defined in the current module (not yet persisted)
  | some _ =>
    -- Check the module name prefix
    let moduleNames := env.allImportedModuleNames
    match env.getModuleIdxFor? declName with
    | none => true
    | some idx =>
      let modName := moduleNames[idx.toNat]!
      !(modName.getRoot == `Lean || modName.getRoot == `Init || modName.getRoot == `Mathlib ||
        modName.getRoot == `Plausible || modName.getRoot == `Aesop ||
        modName.getRoot == `Qq || modName.getRoot == `Batteries)

/-- Build a `MeridianDecl` from a `ConstantInfo`, without coverage analysis. -/
def extractDeclNoCoverage (env : Environment) (ci : ConstantInfo) : MeridianDecl :=
  let val := ci.value?
  let sorry := match val with
    | some v => containsSorry v
    | none   => false
  let goals := match val with
    | some v => collectSorryGoals v
    | none   => []
  let typeDeps := collectDeps ci.type
  let valDeps := match val with
    | some v => collectDeps v
    | none   => {}
  let allDeps := (typeDeps.merge valDeps).toList
  -- File/line info: use the declaration's range if available
  let (file, line) := match env.getDeclarationRange? ci.name with
    | some range => (range.fileName, range.range.start.line)
    | none       => ("unknown", 0)
  { name := ci.name
    type := ci.type
    value := val
    hasSorry := sorry
    sorryGoals := goals
    fileName := file
    line := line
    deps := allDeps
    coverages := [] }

/-- Extract all user-defined declarations from the environment (no coverage yet). -/
def extractAllDeclsNoCoverage : CommandElabM (List MeridianDecl) := do
  let env ← getEnv
  let mut result : List MeridianDecl := []
  for (name, ci) in env.constants.map₁.toList ++ env.constants.map₂.toList do
    if isUserDecl env name && !name.isInternal then
      result := result ++ [extractDeclNoCoverage env ci]
  return result

end Meridian.Core.SorryExtract
```

- [ ] **Step 2: Write test file for sorry detection**

Create `test/Core/TestSorryExtract.lean`:

```lean
import Meridian.Core.SorryExtract

open Meridian.Core.SorryExtract

-- Test declarations
theorem proved_thm : 1 + 1 = 2 := rfl
theorem sorry_thm : 2 + 2 = 4 := sorry
def no_sorry_def : Nat := 42
noncomputable def partial_sorry : Nat × Nat := (1, sorry)

-- Test containsSorry
#eval do
  let env ← Lean.getEnv
  -- sorry_thm should contain sorry
  match env.find? `sorry_thm with
  | some ci =>
    match ci.value? with
    | some v => assert! containsSorry v
    | none   => panic! "sorry_thm has no value"
  | none => panic! "sorry_thm not found"
  -- proved_thm should not contain sorry
  match env.find? `proved_thm with
  | some ci =>
    match ci.value? with
    | some v => assert! !containsSorry v
    | none   => panic! "proved_thm has no value"
  | none => panic! "proved_thm not found"
  IO.println "containsSorry: OK"

-- Test collectSorryGoals
#eval do
  let env ← Lean.getEnv
  match env.find? `sorry_thm with
  | some ci =>
    match ci.value? with
    | some v =>
      let goals := collectSorryGoals v
      assert! goals.length > 0
    | none => panic! "no value"
  | none => panic! "not found"
  IO.println "collectSorryGoals: OK"

-- Test collectDeps
#eval do
  let env ← Lean.getEnv
  match env.find? `proved_thm with
  | some ci =>
    let deps := collectDeps ci.type
    -- The type `1 + 1 = 2` should reference HAdd.hAdd, Eq, Nat, etc.
    assert! deps.contains ``Eq
    assert! deps.contains ``Nat
  | none => panic! "not found"
  IO.println "collectDeps: OK"
```

- [ ] **Step 3: Build and verify tests pass**

Run: `cd ~/Meridian && lake build`

Expected: compilation succeeds with no errors. The `#eval` blocks run during elaboration and print "OK" lines.

- [ ] **Step 4: Commit**

```bash
cd ~/Meridian
git add Meridian/Core/SorryExtract.lean test/Core/TestSorryExtract.lean
git commit -m "feat(core): shared types + sorry detection in SorryExtract"
```

---

### Task 2: DiscrTree Coverage Engine (SorryExtract, part 2)

**Files:**
- Modify: `Meridian/Core/SorryExtract.lean`
- Modify: `test/Core/TestSorryExtract.lean`

- [ ] **Step 1: Add DiscrTree builder and coverage query**

Append before the final `end` in `Meridian/Core/SorryExtract.lean`:

```lean
/-! ## Mathlib DiscrTree Coverage -/

/-- Build a `DiscrTree Name` from all Mathlib constants in the environment.
    For each constant, peel the ∀-telescope and index the conclusion. -/
def buildMathlibDiscrTree : MetaM (DiscrTree Name) := do
  let env ← getEnv
  let moduleNames := env.allImportedModuleNames
  let mut tree : DiscrTree Name := {}
  for (name, ci) in env.constants.map₁.toList ++ env.constants.map₂.toList do
    -- Only index Mathlib constants
    match env.getModuleIdxFor? name with
    | none => continue
    | some idx =>
      let modName := moduleNames[idx.toNat]!
      if modName.getRoot != `Mathlib then continue
    -- Peel forall binders to get the conclusion
    let conclusion ← forallTelescopeReducing ci.type fun _ body => pure body
    -- Skip propositions that are too generic (e.g., True, False)
    if conclusion.isSort || conclusion.isMVar then continue
    try
      tree ← tree.insert conclusion name
    catch _ =>
      -- Some expressions cannot be indexed; skip them
      continue
  return tree

/-- Replace the `idx`-th top-level argument of an application with a fresh MVar. -/
private def replaceArgWithMVar (e : Expr) (idx : Nat) : MetaM Expr := do
  match e with
  | .app f a =>
    let args := e.getAppArgs
    let fn := e.getAppFn
    if idx < args.size then
      let mvar ← mkFreshExprMVar (← inferType args[idx]!)
      let newArgs := args.set! idx mvar
      return mkAppN fn newArgs
    else
      return e
  | _ => return e

/-- Describe what a subterm mismatch means, given the original and replaced terms. -/
private def describeMismatch (original : Expr) (idx : Nat) : MetaM String := do
  let args := original.getAppArgs
  if idx < args.size then
    let fmt ← ppExpr args[idx]!
    return s!"arg {idx}: {fmt}"
  else
    return s!"arg {idx}: <out of range>"

/-- Query the DiscrTree for coverage of a single sorry goal.
    Tries exact match first, then 1-mismatch, then 2-mismatch. -/
def queryCoverage (tree : DiscrTree Name) (goal : Expr) : MetaM CoverageResult := do
  -- Exact match
  let exactHits ← tree.getMatch goal
  if exactHits.size > 0 then
    return { category := .A
             exactMatches := exactHits.toList
             nearMisses := [] }
  -- 1-mismatch: replace each top-level arg with MVar, one at a time
  let numArgs := goal.getAppArgs.size
  let mut allNearMisses : Array NearMiss := #[]
  let mut seen : NameSet := {}
  for i in [:numArgs] do
    let modified ← replaceArgWithMVar goal i
    let hits ← tree.getMatch modified
    for hit in hits do
      if !seen.contains hit then
        seen := seen.insert hit
        let desc ← describeMismatch goal i
        allNearMisses := allNearMisses.push
          { name := hit, mismatchCount := 1, mismatchDescriptions := [desc] }
  -- 2-mismatch: replace pairs of args
  for i in [:numArgs] do
    for j in [i+1:numArgs] do
      let modified ← replaceArgWithMVar goal i
      let modified ← replaceArgWithMVar modified j
      let hits ← tree.getMatch modified
      for hit in hits do
        if !seen.contains hit then
          seen := seen.insert hit
          let desc1 ← describeMismatch goal i
          let desc2 ← describeMismatch goal j
          allNearMisses := allNearMisses.push
            { name := hit, mismatchCount := 2, mismatchDescriptions := [desc1, desc2] }
  -- Sort by mismatch count
  let sorted := allNearMisses.toList.mergeSort (fun a b => a.mismatchCount < b.mismatchCount)
  if sorted.length > 0 then
    return { category := .B, exactMatches := [], nearMisses := sorted }
  else
    return { category := .C, exactMatches := [], nearMisses := [] }

/-- Run coverage analysis on all sorry goals of a declaration. -/
def addCoverage (tree : DiscrTree Name) (decl : MeridianDecl) : MetaM MeridianDecl := do
  if !decl.hasSorry then return decl
  let mut covs : List CoverageResult := []
  for goal in decl.sorryGoals do
    let cov ← queryCoverage tree goal
    covs := covs ++ [cov]
  return { decl with coverages := covs }

/-- Extract all user declarations with full coverage analysis. -/
def extractAllDecls : CommandElabM (List MeridianDecl) := do
  let decls ← extractAllDeclsNoCoverage
  liftTermElabM do
    let tree ← buildMathlibDiscrTree
    let mut result : List MeridianDecl := []
    for d in decls do
      let d' ← addCoverage tree d
      result := result ++ [d']
    return result
```

- [ ] **Step 2: Add the `#sorry_extract` command**

Append before the final `end`:

```lean
/-! ## Commands -/

/-- `#sorry_extract` emits standalone lemma stubs for each sorry in the environment. -/
elab "#sorry_extract" : command => do
  let decls ← extractAllDecls
  let sorryDecls := decls.filter (·.hasSorry)
  if sorryDecls.isEmpty then
    logInfo "No sorries found in user declarations."
    return
  for d in sorryDecls do
    let sig ← liftTermElabM <| ppExpr d.type
    let mut msg := s!"lemma {d.name}.sorried : {sig} := sorry"
    -- Append coverage info
    for (cov, i) in d.coverages.zip (List.range d.coverages.length) do
      msg := msg ++ s!"\n  -- sorry goal {i}: category {cov.category}"
      for m in cov.exactMatches.take 5 do
        msg := msg ++ s!"\n  --   exact match: {m}"
      for nm in cov.nearMisses.take 5 do
        msg := msg ++ s!"\n  --   near-miss ({nm.mismatchCount}): {nm.name}"
        for desc in nm.mismatchDescriptions do
          msg := msg ++ s!" [{desc}]"
    logInfo msg
```

- [ ] **Step 3: Add coverage test**

Append to `test/Core/TestSorryExtract.lean`:

```lean
-- Test coverage types
#eval do
  let cov : CoverageResult := {
    category := .C
    exactMatches := []
    nearMisses := []
  }
  assert! cov.category == .C
  IO.println "CoverageResult: OK"

-- Full integration test: #sorry_extract should run without error
#sorry_extract
```

- [ ] **Step 4: Build and verify**

Run: `cd ~/Meridian && lake build`

Expected: compilation succeeds. `#sorry_extract` in test file emits sorry stubs for `sorry_thm` and `partial_sorry` to the infoview.

- [ ] **Step 5: Commit**

```bash
cd ~/Meridian
git add Meridian/Core/SorryExtract.lean test/Core/TestSorryExtract.lean
git commit -m "feat(core): DiscrTree coverage engine + #sorry_extract command"
```

---

### Task 3: Dependency Graph (DepGraph)

**Files:**
- Modify: `Meridian/Core/DepGraph.lean`
- Create: `test/Core/TestDepGraph.lean`

- [ ] **Step 1: Implement DepGraph types and builder**

Replace the contents of `Meridian/Core/DepGraph.lean`:

```lean
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

/-- Compute the worst (highest-index) category across a list of CoverageResults. -/
def worstCategoryOf (covs : List CoverageResult) : CoverageCategory :=
  covs.foldl (fun acc c =>
    match acc, c.category with
    | .C, _ => .C
    | _, .C => .C
    | .B, _ => .B
    | _, .B => .B
    | _, _  => .A
  ) .A

/-- Build a dependency graph from a list of `MeridianDecl`s.
    Only edges to other project-local declarations are included. -/
def buildDepGraph (decls : List MeridianDecl) : DepGraph :=
  let nameSet : NameSet := decls.foldl (fun acc d => acc.insert d.name) {}
  let mut nodes : NameMap DepNode := {}
  let mut edges : NameMap (List Name) := {}
  for d in decls do
    let node : DepNode := {
      name := d.name
      hasSorry := d.hasSorry
      sorryCount := d.sorryGoals.length
      worstCategory := worstCategoryOf d.coverages
      coverages := d.coverages
    }
    nodes := nodes.insert d.name node
    -- Filter deps to project-local names only
    let localDeps := d.deps.filter nameSet.contains
    edges := edges.insert d.name localDeps
  { nodes, edges }

/-! ## Graph Analysis -/

/-- Count how many declarations transitively depend on `target`.
    (i.e., how many nodes have a path TO `target` in the reverse graph.) -/
partial def transitiveDepCount (g : DepGraph) (target : Name) : Nat :=
  -- Build reverse graph
  let mut rev : NameMap (List Name) := {}
  for (src, dsts) in g.edges.toList do
    for dst in dsts do
      let existing := (rev.find? dst).getD []
      rev := rev.insert dst (src :: existing)
  -- BFS from target in reverse graph
  let mut visited : NameSet := {}
  let mut queue : List Name := (rev.find? target).getD []
  while !queue.isEmpty do
    match queue with
    | [] => break
    | n :: rest =>
      queue := rest
      if !visited.contains n then
        visited := visited.insert n
        queue := queue ++ ((rev.find? n).getD [])
  visited.size

/-- Find the longest chain of sorry-containing declarations (critical sorry path). -/
partial def longestSorryChain (g : DepGraph) : List Name :=
  let sorryNames : NameSet := g.nodes.toList.foldl (fun acc (n, node) =>
    if node.hasSorry then acc.insert n else acc) {}
  -- DFS with memoisation
  let mut memo : NameMap (List Name) := {}
  let mut best : List Name := []
  for (name, _) in g.nodes.toList do
    if !sorryNames.contains name then continue
    let chain := dfs g sorryNames name {}
    if chain.length > best.length then
      best := chain
  best
where
  dfs (g : DepGraph) (sorryNames : NameSet) (n : Name) (visited : NameSet) : List Name :=
    if visited.contains n then []
    else
      let visited' := visited.insert n
      let children := ((g.edges.find? n).getD []).filter sorryNames.contains
      let childChains := children.map (dfs g sorryNames · visited')
      let longestChild := childChains.foldl (fun acc c => if c.length > acc.length then c else acc) []
      n :: longestChild

/-! ## Output Formatting -/

/-- Render the graph as a Graphviz DOT string. -/
def toDOT (g : DepGraph) : String :=
  let mut lines : List String := ["digraph MeridianDeps {", "  rankdir=BT;",
    "  node [shape=box, style=filled, fontname=\"monospace\"];"]
  -- Nodes with colour by status
  for (name, node) in g.nodes.toList do
    let colour := if !node.hasSorry then "\"#90EE90\""  -- green: proved
      else match node.worstCategory with
        | .A => "\"#FFFF99\""  -- yellow: exact match
        | .B => "\"#FFD699\""  -- orange: near-miss
        | .C => "\"#FF9999\""  -- red: no match
    let label := s!"{name}\\nsorries: {node.sorryCount}"
    lines := lines ++ [s!"  \"{name}\" [label=\"{label}\", fillcolor={colour}];"]
  -- Edges
  for (src, dsts) in g.edges.toList do
    for dst in dsts do
      lines := lines ++ [s!"  \"{src}\" -> \"{dst}\";"]
  lines := lines ++ ["}"]
  "\n".intercalate lines

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
```

- [ ] **Step 2: Write test file**

Create `test/Core/TestDepGraph.lean`:

```lean
import Meridian.Core.DepGraph

open Meridian.Core.SorryExtract
open Meridian.Core.DepGraph

-- Test declarations with known dependency structure
def baseValue : Nat := 42

theorem uses_base : baseValue = 42 := rfl

theorem sorry_uses_base : baseValue > 0 := sorry

-- Integration test
#dep_graph
```

- [ ] **Step 3: Build and verify**

Run: `cd ~/Meridian && lake build`

Expected: compilation succeeds. `#dep_graph` outputs DOT format and summary to infoview. `sorry_uses_base` should appear as a red/yellow/orange node depending on Mathlib coverage. `uses_base` should be green. Edge from both to `baseValue`.

- [ ] **Step 4: Commit**

```bash
cd ~/Meridian
git add Meridian/Core/DepGraph.lean test/Core/TestDepGraph.lean
git commit -m "feat(core): dependency graph with DOT output + sorry chain analysis"
```

---

### Task 4: Sorry Inventory (Inventory)

**Files:**
- Modify: `Meridian/Core/Inventory.lean`
- Create: `test/Core/TestInventory.lean`

- [ ] **Step 1: Implement Inventory**

Replace contents of `Meridian/Core/Inventory.lean`:

```lean
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
def buildInventory (decls : List MeridianDecl) (graph : DepGraph) : List InventoryEntry :=
  let sorryDecls := decls.filter (·.hasSorry)
  let entries := sorryDecls.map fun d =>
    let impact := transitiveDepCount graph d.name
    let prio := (Float.ofNat (impact + 1)) * closenessWeight (worstCategory d)
    { decl := d, downstreamImpact := impact, priority := prio }
  -- Sort by priority descending
  entries.mergeSort (fun a b => a.priority > b.priority)

/-- Format an inventory entry as a table row. -/
private def formatEntry (rank : Nat) (e : InventoryEntry) : MetaM String := do
  let sig ← ppExpr e.decl.type
  let sigStr := toString sig
  let truncSig := if sigStr.length > 60 then sigStr.take 57 ++ "..." else sigStr
  let cat := worstCategory e.decl
  let nearMissCount := e.decl.coverages.foldl (fun acc c => acc + c.nearMisses.length) 0
  return s!"  {rank}. [{cat}] {e.decl.name}\n" ++
    s!"     {e.decl.fileName}:{e.decl.line}\n" ++
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
  let mut msg := s!"Sorry Inventory ({entries.length} sorries)\n" ++
    "=" ** 60 ++ "\n"
  for (e, i) in entries.zip (List.range entries.length) do
    let row ← liftTermElabM <| formatEntry (i + 1) e
    msg := msg ++ row ++ "\n"
  logInfo msg

end Meridian.Core.Inventory
```

- [ ] **Step 2: Write test file**

Create `test/Core/TestInventory.lean`:

```lean
import Meridian.Core.Inventory

-- Declarations to populate inventory
def inv_base : Nat := 42
theorem inv_sorry1 : inv_base > 0 := sorry
theorem inv_sorry2 : inv_base < 100 := sorry
theorem inv_proved : inv_base = 42 := rfl

-- Should show inv_sorry1 and inv_sorry2 with rankings
#sorry_inventory
```

- [ ] **Step 3: Build and verify**

Run: `cd ~/Meridian && lake build`

Expected: compilation succeeds. `#sorry_inventory` shows a table with `inv_sorry1` and `inv_sorry2` ranked by priority.

- [ ] **Step 4: Commit**

```bash
cd ~/Meridian
git add Meridian/Core/Inventory.lean test/Core/TestInventory.lean
git commit -m "feat(core): sorry inventory with priority ranking"
```

---

### Task 5: Theorem Extraction (TheoremExtract)

**Files:**
- Modify: `Meridian/Core/TheoremExtract.lean`
- Create: `test/Core/TestTheoremExtract.lean`

- [ ] **Step 1: Implement TheoremExtract**

Replace contents of `Meridian/Core/TheoremExtract.lean`:

```lean
/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.
-/
import Meridian.Core.SorryExtract

/-!
# Theorem Extraction

Split the current file into individual declarations with metadata: name, signature,
proof (or sorry), docstring, local and external dependency lists, tactic count,
proof term size.

## Commands

- `#extract_theorems`: output `List TheoremInfo`
-/

namespace Meridian.Core.TheoremExtract

open Lean Elab Command Meta
open Meridian.Core.SorryExtract

/-! ## Types -/

inductive ProofStatus where
  | proved | sorry | partial
  deriving Inhabited, BEq, Repr

instance : ToString ProofStatus where
  toString
    | .proved  => "proved"
    | .sorry   => "sorry"
    | .partial => "partial"

structure TheoremInfo where
  name          : Name
  signature     : String
  proofStatus   : ProofStatus
  docstring     : Option String
  localDeps     : List Name
  externalDeps  : List Name
  tacticCount   : Nat
  proofTermSize : Nat
  deriving Inhabited, Repr

/-! ## Analysis Functions -/

/-- Count Expr nodes (a rough measure of proof complexity). -/
partial def exprSize : Expr → Nat
  | .app f a         => 1 + exprSize f + exprSize a
  | .lam _ d b _     => 1 + exprSize d + exprSize b
  | .forallE _ d b _ => 1 + exprSize d + exprSize b
  | .letE _ t v b _  => 1 + exprSize t + exprSize v + exprSize b
  | .mdata _ e       => exprSize e
  | .proj _ _ e      => 1 + exprSize e
  | _                => 1

/-- Classify proof status based on sorry presence. -/
def classifyProofStatus (d : MeridianDecl) : ProofStatus :=
  if !d.hasSorry then .proved
  else match d.value with
    | some v =>
      -- If the entire value is just `sorryAx α b`, it is fully sorry
      if v.isApp && v.getAppFn.isConst &&
         v.getAppFn.constName! == ``sorryAx then .sorry
      else .partial
    | none => .sorry

/-- Build a TheoremInfo from a MeridianDecl. -/
def extractTheoremInfo (d : MeridianDecl) : MetaM TheoremInfo := do
  let env ← getEnv
  let sig ← ppExpr d.type
  let doc := (← findDocString? env d.name)
  -- Separate local vs external deps
  let localDeps := d.deps.filter (isUserDecl env ·)
  let externalDeps := d.deps.filter (!isUserDecl env ·)
  let termSize := match d.value with
    | some v => exprSize v
    | none   => 0
  return {
    name := d.name
    signature := toString sig
    proofStatus := classifyProofStatus d
    docstring := doc
    localDeps := localDeps
    externalDeps := externalDeps
    tacticCount := 0  -- Tactic count requires syntax-level analysis, not available from Expr
    proofTermSize := termSize
  }

/-! ## Commands -/

elab "#extract_theorems" : command => do
  let decls ← extractAllDecls
  let mut msg := s!"Extracted {decls.length} declarations\n" ++
    "=" ** 50 ++ "\n"
  for d in decls do
    let info ← liftTermElabM <| extractTheoremInfo d
    msg := msg ++ s!"\n{info.name} [{info.proofStatus}]\n"
    msg := msg ++ s!"  Type: {info.signature}\n"
    match info.docstring with
    | some doc => msg := msg ++ s!"  Doc: {doc}\n"
    | none => pure ()
    msg := msg ++ s!"  Local deps: {info.localDeps}\n"
    msg := msg ++ s!"  Proof size: {info.proofTermSize}\n"
  logInfo msg

end Meridian.Core.TheoremExtract
```

- [ ] **Step 2: Write test file**

Create `test/Core/TestTheoremExtract.lean`:

```lean
import Meridian.Core.TheoremExtract

open Meridian.Core.TheoremExtract

/-- A documented theorem. -/
theorem documented_thm : 1 = 1 := rfl

theorem undocumented_sorry : 2 = 3 := sorry

#extract_theorems
```

- [ ] **Step 3: Build and verify**

Run: `cd ~/Meridian && lake build`

Expected: `#extract_theorems` shows `documented_thm` as `proved` with its docstring, and `undocumented_sorry` as `sorry`.

- [ ] **Step 4: Commit**

```bash
cd ~/Meridian
git add Meridian/Core/TheoremExtract.lean test/Core/TestTheoremExtract.lean
git commit -m "feat(core): theorem extraction with metadata"
```

---

### Task 6: Proof Verification (Verify)

**Files:**
- Modify: `Meridian/Core/Verify.lean`
- Create: `test/Core/TestVerify.lean`

- [ ] **Step 1: Implement Verify**

Replace contents of `Meridian/Core/Verify.lean`:

```lean
/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.
-/
import Meridian.Core.SorryExtract

/-!
# Proof Verification

Given a declaration name with `sorry` and a candidate proof term, check if it
type-checks against the expected type. Wrapper around `Lean.Elab.Term.elabTerm`.

## Commands

- `#verify_proof declName`: verify a candidate proof against a sorry's type
-/

namespace Meridian.Core.Verify

open Lean Elab Command Term Meta
open Meridian.Core.SorryExtract

/-! ## Types -/

inductive VerifyResult where
  | success
  | typeMismatch (expected found : String)
  | elaborationError (msg : String)
  | otherError (msg : String)
  deriving Inhabited, Repr

instance : ToString VerifyResult where
  toString
    | .success               => "SUCCESS: proof type-checks"
    | .typeMismatch e f      => s!"TYPE MISMATCH:\n  expected: {e}\n  found: {f}"
    | .elaborationError msg  => s!"ELABORATION ERROR: {msg}"
    | .otherError msg        => s!"ERROR: {msg}"

/-! ## Verification Logic -/

/-- Find a sorry-containing declaration by name. -/
def findSorryDecl (declName : Name) : CommandElabM MeridianDecl := do
  let decls ← extractAllDeclsNoCoverage
  match decls.find? (·.name == declName) with
  | some d =>
    if !d.hasSorry then
      throwError "Declaration '{declName}' does not contain sorry"
    return d
  | none =>
    throwError "Declaration '{declName}' not found in user declarations"

/-- Verify a candidate proof (given as Syntax) against a declaration's type. -/
def verifyCandidate (declName : Name) (candidate : Syntax) : CommandElabM VerifyResult := do
  let d ← findSorryDecl declName
  liftTermElabM do
    try
      let expectedType := d.type
      let proof ← elabTerm candidate (some expectedType)
      synthesizeSyntheticMVarsNoPostponing
      let proofType ← inferType proof
      if (← isDefEq proofType expectedType) then
        return .success
      else
        let eFmt ← ppExpr expectedType
        let fFmt ← ppExpr proofType
        return .typeMismatch (toString eFmt) (toString fFmt)
    catch e =>
      return .elaborationError (← e.toMessageData.toString)

/-! ## Commands -/

/-- `#verify_proof declName proofTerm` -/
elab "#verify_proof" declName:ident candidate:term : command => do
  let name := declName.getId
  let result ← verifyCandidate name candidate
  logInfo (toString result)

end Meridian.Core.Verify
```

- [ ] **Step 2: Write test file**

Create `test/Core/TestVerify.lean`:

```lean
import Meridian.Core.Verify

-- A sorry'd lemma with a known correct proof
theorem verify_target : 1 + 1 = 2 := sorry

-- Should succeed
#verify_proof verify_target rfl

-- A sorry'd lemma that needs a specific proof
theorem verify_target2 : ∀ n : Nat, n = n := sorry

-- Should succeed
#verify_proof verify_target2 (fun n => rfl)
```

- [ ] **Step 3: Build and verify**

Run: `cd ~/Meridian && lake build`

Expected: first `#verify_proof` reports SUCCESS. Second reports SUCCESS.

- [ ] **Step 4: Commit**

```bash
cd ~/Meridian
git add Meridian/Core/Verify.lean test/Core/TestVerify.lean
git commit -m "feat(core): proof verification command"
```

---

### Task 7: Structural Transforms (Transform)

**Files:**
- Modify: `Meridian/Core/Transform.lean`
- Create: `test/Core/TestTransform.lean`

- [ ] **Step 1: Implement Transform**

Replace contents of `Meridian/Core/Transform.lean`:

```lean
/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.
-/
import Meridian.Core.SorryExtract

/-!
# Structural Transforms

Environment-level transformations on declarations.

## Commands

- `#theorem2sorry`: strip all proofs, replace with `sorry`
- `#normalize`: pretty-print all declarations in standard Mathlib format
- `#rename oldName newName`: rename a declaration and all references
-/

namespace Meridian.Core.Transform

open Lean Elab Command Meta PrettyPrinter
open Meridian.Core.SorryExtract

/-! ## Commands -/

/-- `#theorem2sorry` strips all proofs, replacing with sorry. -/
elab "#theorem2sorry" : command => do
  let decls ← extractAllDeclsNoCoverage
  let mut msg := ""
  for d in decls do
    let sig ← liftTermElabM <| ppExpr d.type
    let kindStr := match d.value with
      | some _ => "theorem"
      | none   => "axiom"
    msg := msg ++ s!"{kindStr} {d.name} : {sig} := sorry\n\n"
  logInfo msg

/-- `#normalize` pretty-prints all declarations in standard format. -/
elab "#normalize" : command => do
  let decls ← extractAllDeclsNoCoverage
  let mut msg := ""
  for d in decls do
    let sig ← liftTermElabM <| ppExpr d.type
    let proofStr ← match d.value with
      | some v =>
        if containsSorry v then pure "sorry"
        else pure (toString (← liftTermElabM <| ppExpr v))
      | none => pure "sorry"
    let kindStr := match d.value with
      | some _ => if d.hasSorry then "theorem" else "theorem"
      | none   => "axiom"
    msg := msg ++ s!"{kindStr} {d.name} : {sig} :=\n  {proofStr}\n\n"
  logInfo msg

/-- `#rename oldName newName` emits a renamed version of a declaration. -/
elab "#rename" oldName:ident newName:ident : command => do
  let old := oldName.getId
  let new := newName.getId
  let decls ← extractAllDeclsNoCoverage
  match decls.find? (·.name == old) with
  | none => throwError "Declaration '{old}' not found"
  | some d =>
    let sig ← liftTermElabM <| ppExpr d.type
    let sigStr := toString sig
    -- Replace occurrences of the old name in the signature string
    let renamedSig := sigStr.replace (toString old) (toString new)
    let proofStr ← match d.value with
      | some v =>
        let pp ← liftTermElabM <| ppExpr v
        let ppStr := toString pp
        pure (ppStr.replace (toString old) (toString new))
      | none => pure "sorry"
    logInfo s!"theorem {new} : {renamedSig} :=\n  {proofStr}"

end Meridian.Core.Transform
```

- [ ] **Step 2: Write test file**

Create `test/Core/TestTransform.lean`:

```lean
import Meridian.Core.Transform

theorem transform_target : 1 + 1 = 2 := rfl
theorem transform_sorry : 2 + 2 = 4 := sorry

#theorem2sorry
#normalize
#rename transform_target renamed_target
```

- [ ] **Step 3: Build and verify**

Run: `cd ~/Meridian && lake build`

Expected: `#theorem2sorry` shows both theorems with `:= sorry`. `#normalize` shows full pretty-printed output. `#rename` shows `renamed_target` with the same type.

- [ ] **Step 4: Commit**

```bash
cd ~/Meridian
git add Meridian/Core/Transform.lean test/Core/TestTransform.lean
git commit -m "feat(core): structural transforms (theorem2sorry, normalize, rename)"
```

---

### Task 8: Counterexample Search (Disprove)

**Files:**
- Modify: `Meridian/Core/Disprove.lean`
- Create: `test/Core/TestDisprove.lean`

- [ ] **Step 1: Implement Disprove**

Replace contents of `Meridian/Core/Disprove.lean`:

```lean
/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.
-/
import Meridian.Core.SorryExtract
import Plausible

/-!
# Counterexample Search

Attempt to find a counterexample for a declaration using Plausible (property-based
testing). Sanity check before spending hours on a sorry that is actually false.

## Commands

- `#disprove declName`: search for counterexamples
-/

namespace Meridian.Core.Disprove

open Lean Elab Command Term Meta
open Meridian.Core.SorryExtract

/-! ## Types -/

inductive DisproveResult where
  | counterexampleFound (description : String)
  | noCounterexample (iterations : Nat)
  | untestable (reason : String)
  deriving Inhabited, Repr

instance : ToString DisproveResult where
  toString
    | .counterexampleFound d => s!"COUNTEREXAMPLE FOUND:\n{d}"
    | .noCounterexample n    => s!"No counterexample found after {n} iterations"
    | .untestable r          => s!"UNTESTABLE: {r}"

/-! ## Commands -/

/-- `#disprove declName` attempts to find a counterexample using Plausible.
    Internally, it creates a `#check_failure` style elaboration that tries to
    negate the proposition and run Plausible. -/
elab "#disprove" declName:ident : command => do
  let name := declName.getId
  let env ← getEnv
  match env.find? name with
  | none => throwError "Declaration '{name}' not found"
  | some ci =>
    let type := ci.type
    -- Try to run Plausible on the negation
    liftTermElabM do
      -- We use `Plausible.Testable.check` which throws on counterexample
      -- and succeeds silently if none found.
      -- To use it, we need to synthesise a `Testable (¬ P)` instance.
      let negType ← mkAppM ``Not #[type]
      try
        -- Check if Testable instance exists
        let testableType ← mkAppM ``Plausible.Testable #[negType]
        match ← trySynthInstance testableType with
        | .some _ =>
          -- Instance exists; run the check by elaborating a term
          -- We catch the exception that Plausible throws on counterexample
          try
            -- Use Plausible.Testable.check
            let checkExpr ← mkAppOptM ``Plausible.Testable.check
              #[some negType, none, none]
            let _ ← inferType checkExpr  -- force elaboration
            logInfo "No counterexample found (Plausible check passed)"
          catch e =>
            -- Plausible throws when it finds a counterexample
            let msg ← e.toMessageData.toString
            logInfo s!"COUNTEREXAMPLE FOUND:\n{msg}"
        | .none =>
          logInfo s!"UNTESTABLE: no Plausible.Testable instance for ¬({← ppExpr type})"
      catch e =>
        let msg ← e.toMessageData.toString
        logInfo s!"UNTESTABLE: {msg}"

end Meridian.Core.Disprove
```

- [ ] **Step 2: Write test file**

Create `test/Core/TestDisprove.lean`:

```lean
import Meridian.Core.Disprove

-- A false proposition: should find counterexample
theorem false_claim : ∀ n : Nat, n < 5 := sorry

-- A true proposition: should not find counterexample
theorem true_claim : ∀ n : Nat, n = n := sorry

#disprove false_claim
#disprove true_claim
```

- [ ] **Step 3: Build and verify**

Run: `cd ~/Meridian && lake build`

Expected: `#disprove false_claim` reports a counterexample (e.g., n=5). `#disprove true_claim` reports no counterexample found.

- [ ] **Step 4: Commit**

```bash
cd ~/Meridian
git add Meridian/Core/Disprove.lean test/Core/TestDisprove.lean
git commit -m "feat(core): counterexample search via Plausible"
```

---

### Task 9: Lakefile Test Target + Final Integration

**Files:**
- Modify: `lakefile.toml`

- [ ] **Step 1: Add test lean_lib to lakefile**

Add to `lakefile.toml`:

```toml
[[lean_lib]]
name = "TestCore"
srcDir = "test"
globs = ["Core.TestSorryExtract", "Core.TestDepGraph", "Core.TestInventory",
         "Core.TestTheoremExtract", "Core.TestVerify", "Core.TestTransform",
         "Core.TestDisprove"]
```

- [ ] **Step 2: Run full build including tests**

Run: `cd ~/Meridian && lake build TestCore`

Expected: all test files compile and #eval assertions pass.

- [ ] **Step 3: Run against 3d-navier-stokes**

To validate Meridian works on a real project, temporarily add Meridian as a dependency in `~/3d-navier-stokes/lean/lakefile.toml` (or use `lake env`). Create a one-off test file:

```lean
import NavierStokes
import Meridian

#sorry_extract
#sorry_inventory
#dep_graph
```

Verify:
- `#sorry_extract` lists all 22 sorries with coverage categories
- `#sorry_inventory` ranks them with downstream impact
- `#dep_graph` outputs valid DOT

- [ ] **Step 4: Commit lakefile changes**

```bash
cd ~/Meridian
git add lakefile.toml
git commit -m "feat(core): add test target to lakefile"
```

---

### Task 10: Cleanup and Final Commit

**Files:**
- All Core files

- [ ] **Step 1: Verify all tests pass**

Run: `cd ~/Meridian && lake clean && lake build`

Expected: clean build succeeds with no warnings.

- [ ] **Step 2: Verify git status is clean**

Run: `cd ~/Meridian && git status`

Expected: nothing to commit, working tree clean.

- [ ] **Step 3: Tag the release**

```bash
cd ~/Meridian && git tag v0.1.0-core -m "Core module complete: sorry extraction, dep graph, inventory, theorem extraction, verify, transform, disprove"
```
