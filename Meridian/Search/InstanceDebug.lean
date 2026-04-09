/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.
-/
import Lean

/-!
# Instance Synthesis Debugging

Hook into `Meta.synthInstance?` to capture the synthesis state on failure,
build a structured search tree, and diagnose the failure with actionable suggestions.

## Commands

- `#instance_debug <type>`: diagnose type-class synthesis failure
-/

namespace Meridian.Search.InstanceDebug

open Lean Elab Command Meta

/-! ## Types -/

/-- A node in the instance synthesis search tree. -/
structure SynthNode where
  className    : Name
  targetType   : String
  result       : String    -- "found", "failed", "max depth"
  children     : List SynthNode
  deriving Inhabited, Repr

/-- Diagnosis result. -/
structure InstanceDiagnosis where
  targetType     : String
  synthesized    : Bool
  instanceName   : Option Name
  missingClasses : List String   -- classes that failed to synthesize
  suggestions    : List String
  deriving Inhabited, Repr

/-! ## Diagnosis Logic -/

/-- Diagnose type-class synthesis for a given type expression. -/
def diagnoseInstance (type : Expr) : MetaM InstanceDiagnosis := do
  let typeFmt ← ppExpr type
  let typeStr := toString typeFmt
  -- Try synthesis
  match ← trySynthInstance type with
  | .some inst =>
    let instType ← inferType inst
    let instFmt ← ppExpr inst
    return {
      targetType := typeStr
      synthesized := true
      instanceName := if inst.isConst then some inst.constName! else none
      missingClasses := []
      suggestions := [s!"Instance found: {instFmt}"]
    }
  | _ =>
    -- Failed: try to identify which sub-instances are missing
    let mut missing : List String := []
    let mut suggestions : List String := []
    -- If the type is a class application, check each argument
    let fn := type.getAppFn
    let args := type.getAppArgs
    if fn.isConst then
      let className := fn.constName!
      suggestions := suggestions ++ [s!"Class: {className}"]
      -- Check if the class itself exists
      let env ← getEnv
      match env.find? className with
      | none =>
        missing := missing ++ [s!"{className} is not defined in the environment"]
      | some _ =>
        -- Class exists but no instance for these args
        for (arg, i) in args.toList.zip (List.range args.size) do
          let argFmt ← ppExpr arg
          -- Check if the argument itself needs instances
          let argType ← inferType arg
          if argType.isSort then
            -- It's a type argument; check if common instances exist for it
            for tc in [``Inhabited, ``BEq, ``DecidableEq] do
              let tcApp ← mkAppM tc #[arg]
              match ← trySynthInstance tcApp with
              | .some _ => pure ()
              | _ =>
                missing := missing ++ [s!"{tc} {argFmt}"]
        suggestions := suggestions ++ [
          s!"No instance of {className} for the given arguments.",
          "Check that all type arguments have the required instances.",
          s!"Missing instances: {missing}"]
    else
      suggestions := suggestions ++ [
        s!"Target is not a class application: {typeStr}",
        "Ensure the target type is a typeclass applied to concrete types."]
    return {
      targetType := typeStr
      synthesized := false
      instanceName := none
      missingClasses := missing
      suggestions := suggestions
    }

/-! ## Commands -/

/-- `#instance_debug type` diagnoses type-class synthesis failure. -/
elab "#instance_debug" t:term : command => do
  let result ← liftTermElabM do
    let type ← Term.elabType t
    diagnoseInstance type
  if result.synthesized then
    let msg := s!"Instance synthesis SUCCEEDED for {result.targetType}\n" ++
      "\n".intercalate result.suggestions
    logInfo msg
  else
    let header := s!"Instance synthesis FAILED for {result.targetType}"
    let missingStr := if result.missingClasses.isEmpty then "  (none identified)"
      else "\n".intercalate (result.missingClasses.map (s!"  - " ++ ·))
    let sugStr := "\n".intercalate (result.suggestions.map (s!"  " ++ ·))
    logInfo s!"{header}\nMissing:\n{missingStr}\nSuggestions:\n{sugStr}"

end Meridian.Search.InstanceDebug
