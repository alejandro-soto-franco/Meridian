/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.
-/
import Lean

/-!
# `lake exe lean-goal-at`

Lake-executable driver that re-elaborates a Lean source file and prints the
mid-proof tactic goal state at a given `(line, col)` source position. The
goal's TYPE is rendered with `Expr.dbgToString` — the SAME debug form
`Meridian.Core.ExportRdf` uses for `mer:typeSignature` (e.g. `Head.{u} arg
arg`, NOT the pretty `ppExpr` form). This keeps the output in the same lexical
space as the stored signatures so the downstream Meridian ranker can match
constants by name.

## Invocation

  lake exe lean-goal-at <SourceFile.lean> <line> <col>

* `<line>` is 1-based, `<col>` is 0-based (Lean's `FileMap` convention:
  `fileMap.ofPosition ⟨line, col⟩` where `Position.line` is 1-based and
  `Position.column` is 0-based).
* On success prints ONE line — the primary (first) goal's type in debug form
  — to STDOUT and exits 0.
* If no goal is found at the position, prints nothing to STDOUT, writes a
  short diagnostic to STDERR, and exits 1.

Must be run from within a project whose lake env exposes the file's import
closure on `LEAN_PATH` (e.g. a project that `require`s Meridian, run via
`lake exe lean-goal-at …` or `lake env <bin> …`), because the driver
re-processes the header and resolves the file's imports against that path.

## Mechanism

Mirrors `Meridian/Drivers/ExportMain.lean`'s IO/search-path setup
(`initSearchPath (← findSysroot)`, `enableInitializersExecution`,
`main : List String → IO UInt32`) but, unlike the export driver, this one
DOES re-run the elaborator (with `InfoState.trees` enabled) so that
`InfoTree.goalsAt?` can recover tactic goal states at a position.
-/

open Lean Lean.Elab

namespace Meridian.Drivers.GoalAt

/-- Print usage to stderr and return exit code 2. -/
private def usage : IO UInt32 := do
  IO.eprintln "usage: lake exe lean-goal-at <SourceFile.lean> <line> <col>"
  IO.eprintln ""
  IO.eprintln "Prints the primary tactic goal's type (Expr.dbgToString form)"
  IO.eprintln "at the given position. <line> is 1-based, <col> is 0-based."
  return 2

end Meridian.Drivers.GoalAt

open Meridian.Drivers.GoalAt

/-- `lake exe lean-goal-at` entry point. -/
unsafe def main (args : List String) : IO UInt32 := do
  let (pathStr, lineStr, colStr) ← match args with
    | [p, l, c] => pure (p, l, c)
    | _ => return ← usage
  let some line := lineStr.toNat?
    | do IO.eprintln s!"lean-goal-at: <line> must be a natural number, got {lineStr}"; return 2
  let some col := colStr.toNat?
    | do IO.eprintln s!"lean-goal-at: <col> must be a natural number, got {colStr}"; return 2
  let path : System.FilePath := pathStr
  if !(← path.pathExists) then
    IO.eprintln s!"lean-goal-at: file not found: {pathStr}"
    return 1

  initSearchPath (← findSysroot)
  Lean.enableInitializersExecution

  let content ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext content path.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  -- Process the header into an Environment, resolving imports against the
  -- LEAN_PATH the lake env supplies (trustLevel 1024 = trust oleans).
  let (env, messages) ← processHeader header {} messages inputCtx (trustLevel := 1024)
  -- Command state with InfoTrees ENABLED so `goalsAt?` has nodes to walk.
  let commandState := Command.mkState env messages {}
  let commandState := { commandState with infoState.enabled := true }
  let s ← IO.processCommands inputCtx parserState commandState
  let trees := s.commandState.infoState.trees.toList

  let fileMap := inputCtx.fileMap
  let pos := fileMap.ofPosition ⟨line, col⟩
  -- Flatten `goalsAt?` over every top-level command's info tree.
  let results : List GoalsAtResult :=
    trees.foldl (init := []) fun acc t => acc ++ InfoTree.goalsAt? fileMap t pos
  let some res := results.head?
    | do
        IO.eprintln s!"lean-goal-at: no tactic goal at {pathStr}:{line}:{col}"
        return 1
  let goals := if res.useAfter then res.tacticInfo.goalsAfter else res.tacticInfo.goalsBefore
  let some mvarId := goals.head?
    | do
        IO.eprintln s!"lean-goal-at: tactic info at {pathStr}:{line}:{col} has no goals \
          ({if res.useAfter then "goalsAfter" else "goalsBefore"} empty)"
        return 1
  -- Render the goal type in the same debug form as the exporter. Run in the
  -- saved ContextInfo's MetaM, using the goal's OWN local context so that
  -- `getType`/`instantiateMVars` see the right hypotheses and mvar assignments.
  let typeStr ← res.ctxInfo.runMetaM {} do
    mvarId.withContext do
      let ty ← mvarId.getType
      let ty ← instantiateMVars ty
      pure (Expr.dbgToString ty)
  IO.println typeStr
  return 0
