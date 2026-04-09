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

open Lean Elab Command Meta
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
    msg := msg ++ s!"theorem {d.name} : {sig} :=\n  {proofStr}\n\n"
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
    let renamedSig := sigStr.replace (toString old) (toString new)
    let proofStr ← match d.value with
      | some v =>
        let pp ← liftTermElabM <| ppExpr v
        let ppStr := toString pp
        pure (ppStr.replace (toString old) (toString new))
      | none => pure "sorry"
    logInfo s!"theorem {new} : {renamedSig} :=\n  {proofStr}"

end Meridian.Core.Transform
