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

end Meridian.Core.SorryExtract
