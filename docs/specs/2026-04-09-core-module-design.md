# Meridian Core Module Design Spec

**Date:** 2026-04-09
**Status:** Approved
**Scope:** `Meridian.Core` (7 files)
**Primary driver:** `~/3d-navier-stokes` formalisation (22 sorries, Leray-Hopf existence + topological regularity)

## Goal

Implement the Core module of Meridian: environment walking, sorry extraction, dependency graph construction, Mathlib coverage analysis via DiscrTree, theorem extraction, proof verification, structural transforms, and counterexample search. All seven files go from empty namespace to working commands/tactics.

## Shared Types

All types defined in `SorryExtract.lean`, re-exported by `Core.lean`.

### MeridianDecl

Per-declaration metadata record.

```
structure MeridianDecl where
  name         : Name
  type         : Expr              -- fully elaborated goal type
  value        : Option Expr       -- proof term; none for axioms/opaque
  hasSorry     : Bool
  sorryGoals   : List Expr         -- goal types at each sorry site
  fileName     : String
  line         : Nat
  deps         : List Name         -- Expr.const references in type + value
  coverages    : List CoverageResult  -- one per sorry goal (empty if no sorry)
  deriving Inhabited
```

### CoverageResult

Mathlib coverage classification for a sorry goal.

```
inductive CoverageCategory where
  | A  -- exact Mathlib match exists (closable with exact?/apply?)
  | B  -- near-miss (1-2 subterm mismatches)
  | C  -- no close match (missing Mathlib infrastructure)
  deriving Inhabited, BEq, Repr

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
```

### DepGraph

Directed dependency graph with annotated nodes.

```
structure DepNode where
  name          : Name
  hasSorry      : Bool
  sorryCount    : Nat
  worstCategory : CoverageCategory  -- worst (highest) category across all sorry goals
  coverages     : List CoverageResult
  deriving Inhabited, Repr

structure DepGraph where
  nodes : NameMap DepNode
  edges : NameMap (List Name)   -- adjacency list: A -> [B, C] means A depends on B, C
  deriving Inhabited
```

### TheoremInfo

Extracted theorem metadata.

```
structure TheoremInfo where
  name          : Name
  signature     : String         -- pretty-printed type
  proofStatus   : ProofStatus    -- proved | sorry | partial (mix of sorry + proof)
  docstring     : Option String
  localDeps     : List Name      -- project-internal references
  externalDeps  : List Name      -- Mathlib/Lean references
  tacticCount   : Nat            -- number of tactic nodes in proof term
  proofTermSize : Nat            -- Expr node count
  deriving Inhabited, Repr

inductive ProofStatus where
  | proved | sorry | partial
  deriving Inhabited, BEq, Repr
```

## Module Specifications

### 1. SorryExtract (`Meridian/Core/SorryExtract.lean`)

**Imports:** `Lean`, `Mathlib.Tactic.Find` (for DiscrTree access)

**Responsibility:** Walk `Environment.constants`, find declarations whose value contains the `sorry` axiom. For each sorry site, extract the goal type. Build `MeridianDecl` records. Provide Mathlib DiscrTree coverage analysis.

**Internal functions:**

- `containsSorry (e : Expr) : Bool` -- recursive Expr walk checking for `Expr.const ``sorryAx ..`
- `collectSorryGoals (e : Expr) : MetaM (List Expr)` -- find sorry sites, return goal types at each
- `collectDeps (e : Expr) : NameSet` -- collect all `Expr.const` names referenced
- `buildMathlibDiscrTree : MetaM (DiscrTree Name)` -- build DiscrTree from all constants whose module path starts with `Mathlib.`
- `queryCoverage (tree : DiscrTree Name) (goal : Expr) : MetaM CoverageResult` -- query with exact match first, then with up to 2 wildcard subterms for near-misses. Exact unification = category A. 1-2 mismatches = B. No hits = C.
- `extractDecl (env : Environment) (tree : DiscrTree Name) (ci : ConstantInfo) : MetaM MeridianDecl` -- build a MeridianDecl from a ConstantInfo
- `extractAllDecls : MetaM (List MeridianDecl)` -- iterate over user-defined constants (filter out Lean/Mathlib internals), produce MeridianDecl for each

**Commands:**

- `#sorry_extract` -- for each sorry-containing `MeridianDecl`, emit a standalone `lemma <name>.sorried : <type> := sorry` stub to the infoview. Universe variables and instance arguments are fully resolved.

**Design notes:**

- The DiscrTree is built once per `#sorry_extract` invocation and cached in a monadic ref for reuse within the same command.
- Near-miss detection: for each sorry goal, try replacing the top-level and first-level subterms with `Expr.mvar` one at a time, query the tree for each variant, collect unique hits, count how many subterms had to be replaced.
- Filtering: only process constants from the current project (not from `Lean.`, `Mathlib.`, `Init.`). Use `Environment.getModuleIdxFor?` to determine provenance.

### 2. DepGraph (`Meridian/Core/DepGraph.lean`)

**Imports:** `Meridian.Core.SorryExtract`

**Responsibility:** Build a directed acyclic graph of declaration dependencies. Annotate nodes with sorry status and Mathlib coverage. Output DOT format and expose `DepGraph` structure.

**Internal functions:**

- `buildDepGraph (decls : List MeridianDecl) : DepGraph` -- construct adjacency list from `MeridianDecl.deps`, filtering to project-local names only. Populate `DepNode` from each decl's sorry/coverage data.
- `transitiveDepCount (g : DepGraph) (n : Name) : Nat` -- count how many declarations transitively depend on `n` (downstream impact).
- `toDOT (g : DepGraph) : String` -- render as Graphviz DOT. Nodes coloured by category: green = proved, red = sorry category C, orange = sorry category B, yellow = sorry category A. Edges show dependency direction.
- `toDepGraphString (g : DepGraph) : String` -- human-readable text summary

**Commands:**

- `#dep_graph` -- build and display the dependency graph in DOT format in the infoview. Also log a text summary with node count, edge count, sorry count by category, and critical path (longest sorry chain).

### 3. Inventory (`Meridian/Core/Inventory.lean`)

**Imports:** `Meridian.Core.SorryExtract`, `Meridian.Core.DepGraph`

**Responsibility:** Produce a prioritised sorry inventory table combining coverage analysis with dependency impact.

**Internal functions:**

- `sorryPriority (decl : MeridianDecl) (impact : Nat) : Float` -- scoring function: `(impact + 1) * closenessWeight(category)` where A=3.0, B=2.0, C=1.0. Higher = more valuable to close.
- `buildInventory (decls : List MeridianDecl) (graph : DepGraph) : List InventoryEntry` -- for each sorry-containing decl, compute priority, sort descending.

**Types:**

```
structure InventoryEntry where
  decl           : MeridianDecl
  downstreamImpact : Nat
  priority       : Float
  deriving Inhabited
```

**Commands:**

- `#sorry_inventory` -- display a table in the infoview: rank, name, file:line, goal type (truncated), category, near-miss count, downstream impact, priority score. Sorted by priority descending.

### 4. TheoremExtract (`Meridian/Core/TheoremExtract.lean`)

**Imports:** `Meridian.Core.SorryExtract`

**Responsibility:** Extract all declarations in the current file into `TheoremInfo` records with metadata.

**Internal functions:**

- `countTactics (e : Expr) : Nat` -- count tactic-mode proof nodes (heuristic: count `Lean.Elab.Tactic` wrapper nodes)
- `exprSize (e : Expr) : Nat` -- count Expr nodes
- `classifyProofStatus (decl : MeridianDecl) : ProofStatus` -- proved if no sorry, sorry if entire value is sorry, partial if sorry exists within a larger proof
- `extractTheoremInfo (decl : MeridianDecl) : MetaM TheoremInfo` -- build TheoremInfo from MeridianDecl

**Commands:**

- `#extract_theorems` -- output `List TheoremInfo` to the infoview, one entry per declaration in the current file

### 5. Verify (`Meridian/Core/Verify.lean`)

**Imports:** `Meridian.Core.SorryExtract`

**Responsibility:** Given a declaration name containing sorry and a candidate proof term, type-check the candidate against the sorry's expected type.

**Internal functions:**

- `findSorryDecl (name : Name) : MetaM MeridianDecl` -- look up the declaration, error if not found or no sorry
- `verifyCandidate (decl : MeridianDecl) (candidate : Syntax) : MetaM VerifyResult` -- elaborate `candidate` against `decl.type` using `Lean.Elab.Term.elabTerm` within the declaration's local context. Return success or structured error.

**Types:**

```
inductive VerifyResult where
  | success
  | typeMismatch (expected found : Expr)
  | elaborationError (msg : String)
  | otherError (msg : String)
  deriving Inhabited, Repr
```

**Commands:**

- `#verify_proof declName` -- verify and report result in infoview

### 6. Transform (`Meridian/Core/Transform.lean`)

**Imports:** `Meridian.Core.SorryExtract`

**Responsibility:** Structural transformations on declarations.

**Commands:**

- `#theorem2sorry` -- for every theorem/def in the current file, pretty-print with the proof replaced by `sorry`. Output to infoview. Useful for generating skeleton files.

- `#normalize` -- pretty-print all declarations in standard Mathlib format (one declaration per block, sorted by dependency order, standard indentation). Output to infoview.

- `#rename oldName newName` -- find the declaration `oldName`, emit a renamed version with all internal self-references updated. Note: this operates on the pretty-printed output, not the environment in-place (Lean 4 does not support mutable environments). Output to infoview.

**Design notes:**

- All three commands produce text output to the infoview. They do not modify files. The user copies the output.
- `#theorem2sorry` preserves the type signature exactly, only replacing the value.
- `#normalize` uses `Lean.PrettyPrinter.ppCommand` or equivalent.
- `#rename` uses string substitution on the pretty-printed output after verifying the old name exists.

### 7. Disprove (`Meridian/Core/Disprove.lean`)

**Imports:** `Meridian.Core.SorryExtract`, `Mathlib.Testing.Plausible` (or `Plausible`)

**Responsibility:** Attempt to find a counterexample for a declaration using Plausible.

**Internal functions:**

- `negateGoal (goal : Expr) : MetaM Expr` -- construct `Not goal` (or if goal is `∀ x, P x`, construct `∃ x, ¬P x` for better Plausible coverage)
- `runPlausible (negatedGoal : Expr) : MetaM DisproveResult` -- use `Plausible.Testable.check` on the negated goal with configurable iteration count (default 1000)

**Types:**

```
inductive DisproveResult where
  | counterexampleFound (description : String)
  | noCounterexample (iterations : Nat)
  | untestable (reason : String)    -- goal type has no Testable instance
  deriving Inhabited, Repr
```

**Commands:**

- `#disprove declName` -- negate the goal, run Plausible, report result. If counterexample found, display it. If no counterexample after N iterations, say so. If the type is not testable, report which `Testable` instance is missing.

## Mathlib DiscrTree Integration Detail

The DiscrTree-based coverage analysis is the most complex piece. Detailed design:

### Building the tree

```
buildMathlibDiscrTree : MetaM (DiscrTree Name)
```

1. Iterate over `(Environment.constants).map₂`
2. Filter to constants where `Environment.getModuleIdxFor?` returns a module in `Mathlib.*`
3. For each constant, get its type. If the type is a `∀`-telescope, peel binders and use the conclusion.
4. Insert `(conclusion, name)` into the DiscrTree.

### Querying

```
queryCoverage (tree : DiscrTree Name) (goal : Expr) : MetaM CoverageResult
```

1. **Exact query:** `tree.getMatch goal`. If non-empty, category = A, populate `exactMatches`.
2. **Near-miss query (1 mismatch):** for each top-level subterm of `goal`, replace it with a fresh `MVar`, query the tree. Collect hits not already in exact matches. Record which subterm was replaced as the mismatch description.
3. **Near-miss query (2 mismatches):** for each pair of top-level subterms, replace both with fresh `MVar`s, query. Collect new hits.
4. If near-misses found, category = B. Otherwise category = C.
5. Deduplicate and sort near-misses by mismatch count ascending.

### Performance

Building the DiscrTree from Mathlib is O(number of Mathlib constants), roughly 100k-200k entries. This takes a few seconds. The tree is built once per command invocation. For `#sorry_inventory`, it is built once and reused across all sorry queries.

## Testing Strategy

Test files under `test/Core/`, one per module:

- `test/Core/TestSorryExtract.lean` -- define 3-4 small declarations (some with sorry, some without), run `#sorry_extract`, verify output via `#eval`
- `test/Core/TestDepGraph.lean` -- define declarations with known dependencies, run `#dep_graph`, verify DOT output contains expected edges
- `test/Core/TestInventory.lean` -- define declarations with known sorry/dep structure, verify ranking
- `test/Core/TestTheoremExtract.lean` -- verify metadata extraction
- `test/Core/TestVerify.lean` -- define a sorry'd lemma and a correct proof, verify `#verify_proof` accepts it. Also test with an incorrect proof.
- `test/Core/TestTransform.lean` -- verify `#theorem2sorry` strips proofs, `#normalize` produces standard output
- `test/Core/TestDisprove.lean` -- define a false lemma (e.g., `∀ n : Nat, n < 5`), verify `#disprove` finds counterexample

Compilation success = command registration works. `#eval`-based assertions = logic correctness.

## Build Order

Implementation proceeds in this order (each file depends only on prior files):

1. `SorryExtract.lean` (shared types + sorry detection + DiscrTree coverage)
2. `DepGraph.lean` (depends on SorryExtract for MeridianDecl)
3. `Inventory.lean` (depends on SorryExtract + DepGraph)
4. `TheoremExtract.lean` (depends on SorryExtract for MeridianDecl)
5. `Verify.lean` (depends on SorryExtract for sorry lookup)
6. `Transform.lean` (depends on SorryExtract for MeridianDecl)
7. `Disprove.lean` (depends on SorryExtract + Plausible)

Files 4-7 are independent of each other and depend only on SorryExtract. They can be implemented in any order after 1-3.

## Non-Goals (deferred to other modules)

- `meridian_suggest`, `meridian_search`, `meridian_decompose` (Search module)
- `#gap_report`, `#mathlib_coverage` with full project aggregation (Analysis module)
- `meridian_distrib`, `meridian_sobolev`, `meridian_biot_savart` (Domain/PDE module)
- File modification (all Core commands output to infoview, never write files)
