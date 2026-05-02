/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.
-/
import Lean
import Mathlib.Tactic.Core

/-!
# DiscrTree Export

Walks every non-internal declaration in the current environment and emits a JSON
array describing each one: `full_name`, `module_path`, `kind`, and the
pretty-printed `discr_tree_key` used by Mathlib's `DiscrTree` indexing.

The primary consumer is `tactic-ranker`, which uses the DiscrTree key as the
sparse retrieval channel of a hybrid dense+structural retriever.

## Commands

- `#discr_tree_export "path/to/out.json"`: write a JSON array of all indexed
  premises. One-shot, offline, data-prep-time.
-/

namespace Meridian.Analysis.DiscrTreeExport

open Lean Elab Command Meta

/-- Render a `DiscrTree.Key` array as a stable `|`-delimited string. -/
private def keyString (ks : Array DiscrTree.Key) : String :=
  "|".intercalate (ks.toList.map (fun k => (repr k).pretty))

/-- Map a `ConstantInfo` to a short `kind` tag. -/
private def kindOf (info : ConstantInfo) : String :=
  match info with
  | .thmInfo    _ => "theorem"
  | .defnInfo   _ => "def"
  | .axiomInfo  _ => "axiom"
  | .quotInfo   _ => "axiom"
  | .inductInfo _ => "inductive"
  | .ctorInfo   _ => "ctor"
  | .recInfo    _ => "rec"
  | .opaqueInfo _ => "opaque"

/-- `#discr_tree_export "path"` dumps indexed premises to a JSON file.
Streams a single JSON array to disk, one row per `,\n`-separated entry, so
elaboration over a full Mathlib environment (~200k constants) does not blow
the stack on a single mega `toString (Json.arr ...)` call. -/
elab "#discr_tree_export " path:str : command => do
  let env ← getEnv
  let h ← IO.FS.Handle.mk path.getString .write
  h.putStr "["
  let mut first := true
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if name.isInternal then
      continue
    let keys ← try
      liftTermElabM (Meta.MetaM.run' (DiscrTree.mkPath info.type))
    catch _ => pure (#[] : Array DiscrTree.Key)
    let modulePath :=
      match env.getModuleFor? name with
      | some m => m.toString
      | none   => ""
    let row : Json := Json.mkObj [
      ("full_name",       Json.str name.toString),
      ("module_path",     Json.str modulePath),
      ("kind",            Json.str (kindOf info)),
      ("discr_tree_key",  Json.str (keyString keys))
    ]
    if first then first := false else h.putStr ",\n"
    h.putStr (toString row)
    count := count + 1
  h.putStr "]\n"
  logInfo m!"wrote {count} premises to {path.getString}"

end Meridian.Analysis.DiscrTreeExport
