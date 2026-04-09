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

elab "#verify_proof" declName:ident candidate:term : command => do
  let name := declName.getId
  let result ← verifyCandidate name candidate
  logInfo (toString result)

end Meridian.Core.Verify
