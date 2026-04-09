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
  | proved
  | hasSorry
  | partialProof
  deriving Inhabited, BEq, Repr

instance : ToString ProofStatus where
  toString
    | .proved      => "proved"
    | .hasSorry    => "sorry"
    | .partialProof => "partial"

structure TheoremInfo where
  name          : Name
  signature     : String
  proofStatus   : ProofStatus
  docstring     : Option String
  localDeps     : List Name
  externalDeps  : List Name
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
         v.getAppFn.constName! == ``sorryAx then .hasSorry
      else .partialProof
    | none => .hasSorry

/-- Build a TheoremInfo from a MeridianDecl. -/
def extractTheoremInfo (d : MeridianDecl) : MetaM TheoremInfo := do
  let env ← getEnv
  let sig ← ppExpr d.type
  let doc := (← findDocString? env d.name)
  let localDeps := d.deps.filter (isCurrentModuleDecl env ·)
  let externalDeps := d.deps.filter (!isCurrentModuleDecl env ·)
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
    proofTermSize := termSize
  }

/-! ## Commands -/

elab "#extract_theorems" : command => do
  let decls ← extractAllDeclsNoCoverage
  let mut msg := s!"Extracted {decls.length} declarations\n" ++
    String.ofList (List.replicate 50 '=') ++ "\n"
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
