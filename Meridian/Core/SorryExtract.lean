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
  | A  -- exact Mathlib match exists
  | B  -- near-miss (1-2 subterm mismatches)
  | C  -- no close match
  deriving Inhabited, BEq, Repr

instance : ToString CoverageCategory where
  toString
    | .A => "A"
    | .B => "B"
    | .C => "C"

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
  | .const n _       => n == ``sorryAx
  | .app f a         => containsSorry f || containsSorry a
  | .lam _ d b _     => containsSorry d || containsSorry b
  | .forallE _ d b _ => containsSorry d || containsSorry b
  | .letE _ t v b _  => containsSorry t || containsSorry v || containsSorry b
  | .mdata _ e       => containsSorry e
  | .proj _ _ e      => containsSorry e
  | _                => false

/-- Collect the type arguments of every `sorryAx` application in an expression.
    `sorryAx` has signature `(α : Sort u) → Bool → α`, so `@sorryAx α b`
    appears as `.app (.app (.const ``sorryAx _) α) b`. We want `α`. -/
partial def collectSorryGoals : Expr → List Expr
  | .app (.app (.const n _) α) _ =>
    if n == ``sorryAx then [α] else []
  | .app f a       => collectSorryGoals f ++ collectSorryGoals a
  | .lam _ d b _   => collectSorryGoals d ++ collectSorryGoals b
  | .forallE _ d b _ => collectSorryGoals d ++ collectSorryGoals b
  | .letE _ t v b _ => collectSorryGoals t ++ collectSorryGoals v ++ collectSorryGoals b
  | .mdata _ e     => collectSorryGoals e
  | .proj _ _ e    => collectSorryGoals e
  | _              => []

/-- Collect all constant `Name`s referenced in an expression. -/
partial def collectDeps (e : Expr) : NameSet :=
  go e {}
where
  go : Expr → NameSet → NameSet
  | .const n _,       acc => acc.insert n
  | .app f a,         acc => go a (go f acc)
  | .lam _ d b _,     acc => go b (go d acc)
  | .forallE _ d b _, acc => go b (go d acc)
  | .letE _ t v b _,  acc => go b (go v (go t acc))
  | .mdata _ e,       acc => go e acc
  | .proj _ _ e,      acc => go e acc
  | _,                acc => acc

/-- Return true if `declName` belongs to a user-defined module (not Lean, Init, Mathlib, etc). -/
def isUserDecl (env : Environment) (declName : Name) : Bool :=
  match env.getModuleIdxFor? declName with
  | none   => true  -- defined in the current module
  | some idx =>
    let moduleNames := env.allImportedModuleNames
    if h : idx.toNat < moduleNames.size then
      let modName := moduleNames[idx.toNat]
      !(modName.getRoot == `Lean || modName.getRoot == `Init || modName.getRoot == `Mathlib ||
        modName.getRoot == `Plausible || modName.getRoot == `Aesop ||
        modName.getRoot == `Qq || modName.getRoot == `Batteries ||
        modName.getRoot == `Meridian)
    else false

/-- Build a `MeridianDecl` from a `ConstantInfo`, without coverage analysis. -/
def extractDeclNoCoverage (ci : ConstantInfo) : MeridianDecl :=
  let val := ci.value?
  let hasSorry := match val with
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
  { name := ci.name
    type := ci.type
    value := val
    hasSorry := hasSorry
    sorryGoals := goals
    fileName := "unknown"
    line := 0
    deps := allDeps
    coverages := [] }

/-- Return true if `declName` is defined in the current module (not imported). -/
def isCurrentModuleDecl (env : Environment) (declName : Name) : Bool :=
  env.getModuleIdxFor? declName |>.isNone

/-- Extract all declarations from the current module (no coverage yet). -/
def extractAllDeclsNoCoverage : CommandElabM (List MeridianDecl) := do
  let env ← getEnv
  let mut result : List MeridianDecl := []
  for (name, ci) in env.constants.map₁.toList ++ env.constants.map₂.toList do
    if isCurrentModuleDecl env name && !name.isInternal then
      result := result ++ [extractDeclNoCoverage ci]
  return result

/-- Extract all user-defined declarations across all imported user modules + current module. -/
def extractAllUserDecls : CommandElabM (List MeridianDecl) := do
  let env ← getEnv
  let mut result : List MeridianDecl := []
  for (name, ci) in env.constants.map₁.toList ++ env.constants.map₂.toList do
    if (isCurrentModuleDecl env name || isUserDecl env name) && !name.isInternal then
      result := result ++ [extractDeclNoCoverage ci]
  return result

/-! ## Mathlib DiscrTree Coverage -/

/-- Build a `DiscrTree Name` from all Mathlib constants in the environment.
    For each constant, peel the forall-telescope and index the conclusion. -/
def buildMathlibDiscrTree : MetaM (DiscrTree Name) := do
  let env ← getEnv
  let moduleNames := env.allImportedModuleNames
  let mut tree : DiscrTree Name := {}
  for (name, ci) in env.constants.map₂.toList do
    match env.getModuleIdxFor? name with
    | none => continue
    | some idx =>
      if h : idx.toNat < moduleNames.size then
        let modName := moduleNames[idx.toNat]
        if modName.getRoot != `Mathlib then continue
      else continue
    -- Peel forall binders to get the conclusion
    let conclusion ← forallTelescopeReducing ci.type fun _ body => pure body
    if conclusion.isSort || conclusion.isMVar then continue
    try
      tree ← tree.insert conclusion name
    catch _ =>
      continue
  return tree

/-- Replace the `idx`-th argument of a function application with a fresh MVar. -/
private def replaceArgWithMVar (e : Expr) (idx : Nat) : MetaM Expr := do
  let args := e.getAppArgs
  let fn := e.getAppFn
  if h : idx < args.size then
    let mvar ← mkFreshExprMVar (← inferType args[idx])
    let newArgs := args.set idx mvar
    return mkAppN fn newArgs
  else
    return e

/-- Describe what the mismatch at position `idx` is. -/
private def describeMismatch (original : Expr) (idx : Nat) : MetaM String := do
  let args := original.getAppArgs
  if h : idx < args.size then
    let fmt ← ppExpr args[idx]
    return s!"arg {idx}: {fmt}"
  else
    return s!"arg {idx}: <out of range>"

/-- Query the DiscrTree for coverage of a single sorry goal. -/
def queryCoverage (tree : DiscrTree Name) (goal : Expr) : MetaM CoverageResult := do
  -- Exact match
  let exactHits ← tree.getMatch goal
  if exactHits.size > 0 then
    return { category := .A, exactMatches := exactHits.toList, nearMisses := [] }
  -- 1-mismatch
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
  -- 2-mismatch
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
  let sorted := allNearMisses.toList.mergeSort (fun a b => a.mismatchCount < b.mismatchCount)
  if !sorted.isEmpty then
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

/-- Extract all current-module declarations with full coverage analysis. -/
def extractAllDecls : CommandElabM (List MeridianDecl) := do
  let decls ← extractAllDeclsNoCoverage
  liftTermElabM do
    let tree ← buildMathlibDiscrTree
    let mut result : List MeridianDecl := []
    for d in decls do
      let d' ← addCoverage tree d
      result := result ++ [d']
    return result

/-- Extract all user declarations (current + imported user modules) with coverage. -/
def extractAllUserDeclsWithCoverage : CommandElabM (List MeridianDecl) := do
  let decls ← extractAllUserDecls
  liftTermElabM do
    let tree ← buildMathlibDiscrTree
    let mut result : List MeridianDecl := []
    for d in decls do
      let d' ← addCoverage tree d
      result := result ++ [d']
    return result

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
    for (cov, i) in d.coverages.zip (List.range d.coverages.length) do
      msg := msg ++ s!"\n  -- sorry goal {i}: category {cov.category}"
      for m in cov.exactMatches.take 5 do
        msg := msg ++ s!"\n  --   exact match: {m}"
      for nm in cov.nearMisses.take 5 do
        msg := msg ++ s!"\n  --   near-miss ({nm.mismatchCount}): {nm.name}"
        for desc in nm.mismatchDescriptions do
          msg := msg ++ s!" [{desc}]"
    logInfo msg

/-- `#sorry_extract_all` scans all imported user modules (not just the current file). -/
elab "#sorry_extract_all" : command => do
  let decls ← extractAllUserDeclsWithCoverage
  let sorryDecls := decls.filter (·.hasSorry)
  if sorryDecls.isEmpty then
    logInfo "No sorries found in user declarations."
    return
  for d in sorryDecls do
    let sig ← liftTermElabM <| ppExpr d.type
    let mut msg := s!"lemma {d.name}.sorried : {sig} := sorry"
    for (cov, i) in d.coverages.zip (List.range d.coverages.length) do
      msg := msg ++ s!"\n  -- sorry goal {i}: category {cov.category}"
      for m in cov.exactMatches.take 5 do
        msg := msg ++ s!"\n  --   exact match: {m}"
      for nm in cov.nearMisses.take 5 do
        msg := msg ++ s!"\n  --   near-miss ({nm.mismatchCount}): {nm.name}"
        for desc in nm.mismatchDescriptions do
          msg := msg ++ s!" [{desc}]"
    logInfo msg

end Meridian.Core.SorryExtract
