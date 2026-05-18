/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.
-/
import Lean
import Meridian.Core.ExportRdf

/-!
# `lake exe export-meridian`

Lake-executable driver that produces a v0.2 Meridian Turtle dump of a Lean
project's environment without spinning up the elaborator. Imports the
requested module list via `Lean.withImportModules` (the same primitive
`importGraph`'s `lake exe graph` uses) and calls
`Meridian.Core.ExportRdf.runDumpIO` on the resulting `Environment`.

## Invocation

  lake exe export-meridian <out.ttl> [Module1 Module2 ...]

* `<out.ttl>` is the destination Turtle path (required).
* The optional module-name arguments are the Lean modules to import. They
  must already be built (`lake build` against the host project). When no
  modules are supplied the driver defaults to importing `Meridian`, which is
  the Lake target's own library and gives Stratum's `cite lean-sync` a
  zero-config sanity check against this repo.

The dump format and ontology are defined by `Meridian/Ontology/meridian.ttl`
(v0.2). Stratum's bridge consumer (`stratum-meridian-bridge`) ingests the
resulting Turtle directly.

## Why this lives outside `CommandElabM`

`#export_rdf` in `Meridian.Core.ExportRdf` runs inside `CommandElabM` and
fetches `← getEnv`. For a Lake executable we need `main : List String → IO
UInt32`, so we obtain the `Environment` from `IO` via `withImportModules`
and pass it to the shared `runDumpIO` core (factored out in P1.7).
-/

open Lean
open Meridian.Core.ExportRdf

namespace Meridian.Drivers.ExportMain

/-- Parse a module name from a CLI argument string. Mirrors the convention
    `importGraph`'s `ModuleName` parser uses: dots split components, every
    component is a string segment. Rejects empty strings. -/
private def parseModuleName (s : String) : Except String Name := do
  if s.isEmpty then
    throw "module name cannot be empty"
  let parts := s.splitOn "."
  if parts.any String.isEmpty then
    throw s!"malformed module name: {s}"
  return parts.foldl (init := Name.anonymous) fun acc part => Name.mkStr acc part

/-- Print usage to stderr and return exit code 2. -/
private def usage : IO UInt32 := do
  IO.eprintln "usage: lake exe export-meridian <out.ttl> [Module1 Module2 ...]"
  IO.eprintln ""
  IO.eprintln "Writes a v0.2 Meridian Turtle dump of the imported environment."
  IO.eprintln "When no modules are listed, defaults to `Meridian`."
  return 2

end Meridian.Drivers.ExportMain

open Meridian.Drivers.ExportMain

/-- `lake exe export-meridian` entry point. -/
unsafe def main (args : List String) : IO UInt32 := do
  let (outPath, moduleArgs) ← match args with
    | [] => return ← usage
    | out :: rest => pure (out, rest)
  let moduleNames : Array Name ← do
    if moduleArgs.isEmpty then
      pure #[`Meridian]
    else
      let mut acc : Array Name := #[]
      for s in moduleArgs do
        match parseModuleName s with
        | .ok n   => acc := acc.push n
        | .error msg =>
          IO.eprintln s!"export-meridian: {msg}"
          return 2
      pure acc
  IO.eprintln s!"export-meridian: importing {moduleNames.size} module(s): {moduleNames.toList}"
  initSearchPath (← findSysroot)
  Lean.enableInitializersExecution
  let imports : Array Import := moduleNames.map (fun n => { module := n })
  let t0 ← IO.monoMsNow
  let (decls, mods, trips) ← withImportModules imports (opts := {}) (trustLevel := 1024)
    fun env => runDumpIO env outPath (fun env n _ => includeConst env n)
  let elapsed := (← IO.monoMsNow) - t0
  IO.eprintln s!"export-meridian: wrote {decls} declarations across {mods} modules \
    ({trips} triples) to {outPath} in {elapsed} ms"
  return 0
