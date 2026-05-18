/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.

Bundled `lake env lean --run` driver stub for Stratum's `cite lean-sync`. v1
is a documenting placeholder; the production driver is the
`lake exe export-meridian` Lake target (P1.7) that calls `runDump` outside
`CommandElabM`.

The v0.2 bridge consumer (~/stratum/crates/stratum-meridian-bridge) expects
either of these invocation shapes to produce a v0.2 Turtle dump on stdout
(or at the path passed as `<out.ttl>`):

  lake env lean --run scripts/export-meridian.lean <out.ttl>
  lake exe export-meridian <out.ttl>

This stub documents the contract; see Meridian.Drivers.ExportMain (P1.7) for
the working implementation.
-/

import Meridian

open Meridian.Core.ExportRdf

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | [outPath] =>
    IO.eprintln s!"export-meridian (stub): would write v0.2 dump to {outPath}"
    IO.eprintln "use `lake exe export-meridian` for the production driver"
    return 0
  | _ =>
    IO.eprintln "usage: lake env lean --run scripts/export-meridian.lean <out.ttl>"
    return 2
