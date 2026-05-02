/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.
-/
import Lean
import Meridian.Core.SorryExtract

/-!
# RDF / SPARQL Export

Streams the current Lean environment to a Turtle (`.ttl`) file aligned to the
Meridian ontology (`Ontology/meridian.ttl`). Each declaration is rendered as a
subject IRI of the form

  <https://meridian.sotofranco.dev/lean/<module-path>#<decl-name>>

with class membership, namespace, sorry status, axiom usage, and direct
dependencies. Output is suitable for loading into Apache Jena Fuseki, Stardog,
GraphDB, or any RDF store.

## Commands

- `#export_rdf "path/to/out.ttl"`: dump the entire environment.
- `#export_rdf_local "path/to/out.ttl"`: dump only declarations defined in the
  current module.
-/

namespace Meridian.Core.ExportRdf

open Lean Elab Command Meta
open Meridian.Core.SorryExtract

/-! ## IRI construction -/

/-- Percent-encode bytes outside the conservative URL-safe set. We keep
    `A-Z a-z 0-9 - _ . ~ /` and `#` (since `#` is the fragment separator we
    deliberately emit). Everything else becomes `%HH`. This is sufficient for
    Lean's standard naming conventions. -/
private def percentEncode (s : String) : String :=
  let safe (c : Char) : Bool :=
    c.isAlphanum || c == '-' || c == '_' || c == '.' || c == '~' || c == '/' || c == '#'
  let hexDigit (n : Nat) : Char :=
    if n < 10 then Char.ofNat (n + '0'.toNat)
    else Char.ofNat (n - 10 + 'A'.toNat)
  let toHex (n : Nat) : String :=
    String.singleton (hexDigit (n / 16)) ++ String.singleton (hexDigit (n % 16))
  s.foldl (init := "") fun acc c =>
    if safe c then acc.push c
    else
      let bytes := (String.singleton c).toUTF8
      bytes.foldl (init := acc) fun a b => a ++ "%" ++ toHex b.toNat

/-- Convert a Lean `Name` (possibly hierarchical) to a flat dot-joined string.
    Anonymous becomes the empty string; numeric components are rendered. -/
private def nameToDotted (n : Name) : String :=
  n.toString (escape := false)

/-- Convert a Lean module name (e.g. `Mathlib.Topology.Basic`) to a path
    component with `/` separators (e.g. `Mathlib/Topology/Basic`). -/
private def modulePath (modName : Name) : String :=
  let parts := modName.componentsRev.reverse.map (·.toString (escape := false))
  "/".intercalate parts

/-- Look up the module a declaration was defined in. Returns `none` for
    declarations defined in the current (not-yet-imported) module. -/
private def moduleOf? (env : Environment) (declName : Name) : Option Name :=
  match env.getModuleIdxFor? declName with
  | none     => none
  | some idx =>
    let mods := env.allImportedModuleNames
    if h : idx.toNat < mods.size then some mods[idx.toNat] else none

/-- Build the IRI of a declaration. If the module is unknown, we synthesise a
    `_local` module path so the IRI remains globally unique within the dump. -/
private def declIri (env : Environment) (declName : Name) : String :=
  let modSlug := match moduleOf? env declName with
    | some m => modulePath m
    | none   => "_local"
  let path := percentEncode modSlug
  let frag := percentEncode (nameToDotted declName)
  s!"<https://meridian.sotofranco.dev/lean/{path}#{frag}>"

/-- Build the IRI of a module. -/
private def moduleIri (modName : Name) : String :=
  let slug := percentEncode (modulePath modName)
  s!"<https://meridian.sotofranco.dev/lean/{slug}>"

/-! ## Classification -/

/-- Map a `ConstantInfo` to the most specific Meridian class. -/
private def classOf (info : ConstantInfo) : String :=
  match info with
  | .thmInfo    _ => "mer:Theorem"
  | .defnInfo   _ => "mer:Definition"
  | .axiomInfo  _ => "mer:Axiom"
  | .quotInfo   _ => "mer:Axiom"
  | .inductInfo _ => "mer:Inductive"
  | .ctorInfo   _ => "mer:Constructor"
  | .recInfo    _ => "mer:Recursor"
  | .opaqueInfo _ => "mer:OpaqueDef"

/-- True if the given constant is an axiom or a quotient primitive. -/
private def isAxiomLike (info : ConstantInfo) : Bool :=
  match info with
  | .axiomInfo _ | .quotInfo _ => true
  | _                          => false

/-- Structural size of an expression (subexpression count). Cheap proxy for
    type complexity that does not require pretty-printing. -/
private partial def exprSize : Expr → Nat
  | .app f a         => 1 + exprSize f + exprSize a
  | .lam _ d b _     => 1 + exprSize d + exprSize b
  | .forallE _ d b _ => 1 + exprSize d + exprSize b
  | .letE _ t v b _  => 1 + exprSize t + exprSize v + exprSize b
  | .mdata _ e       => 1 + exprSize e
  | .proj _ _ e      => 1 + exprSize e
  | _                => 1

/-! ## Turtle escaping -/

/-- Escape a string for use as a Turtle string literal (double-quoted form). -/
private def escapeLiteral (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    match c with
    | '\\' => acc ++ "\\\\"
    | '"'  => acc ++ "\\\""
    | '\n' => acc ++ "\\n"
    | '\r' => acc ++ "\\r"
    | '\t' => acc ++ "\\t"
    | _    => acc.push c

/-! ## Streaming emit -/

/-- Standard Turtle prefix block emitted at the top of every dump. -/
private def prologue : String :=
  "@prefix mer:  <https://meridian.sotofranco.dev/ontology#> .\n" ++
  "@prefix rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .\n" ++
  "@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .\n" ++
  "@prefix xsd:  <http://www.w3.org/2001/XMLSchema#> .\n\n"

/-- Emit triples for a single declaration to the open file handle. Returns
    the number of triples written (used for the summary log). -/
private def emitDecl (h : IO.FS.Handle) (env : Environment) (name : Name)
    (info : ConstantInfo) : IO Nat := do
  let subj := declIri env name
  let cls  := classOf info
  let ns   := nameToDotted name.getPrefix
  let fullName := nameToDotted name
  let hasS := match info.value? with
    | some v => containsSorry v
    | none   => false
  let sorryCount := match info.value? with
    | some v => (collectSorryGoals v).length
    | none   => 0
  let tSize := exprSize info.type

  let directDeps : List Name :=
    let typeDeps := collectDeps info.type
    let valDeps := match info.value? with
      | some v => collectDeps v
      | none   => {}
    (typeDeps.merge valDeps).toList
      |>.filter (fun n => !n.isInternal && n != name)

  let axiomDeps : List Name := directDeps.filter fun n =>
    match env.find? n with
    | some ci => isAxiomLike ci
    | none    => false

  let mut trips : Nat := 0

  -- Type assertion + scalar properties
  h.putStr s!"{subj} a {cls} ;\n"
  trips := trips + 1
  h.putStr s!"  mer:declName \"{escapeLiteral fullName}\" ;\n"
  trips := trips + 1
  if !ns.isEmpty then
    h.putStr s!"  mer:inNamespace \"{escapeLiteral ns}\" ;\n"
    trips := trips + 1
  h.putStr s!"  mer:hasSorry \"{if hasS then "true" else "false"}\"^^xsd:boolean ;\n"
  trips := trips + 1
  if sorryCount > 0 then
    h.putStr s!"  mer:sorryCount \"{sorryCount}\"^^xsd:nonNegativeInteger ;\n"
    trips := trips + 1
  h.putStr s!"  mer:typeSize \"{tSize}\"^^xsd:nonNegativeInteger"
  trips := trips + 1

  -- Module link (closes prior triple with `;` if module known)
  match moduleOf? env name with
  | some m =>
    h.putStr s!" ;\n  mer:inModule {moduleIri m}"
    trips := trips + 1
  | none => pure ()

  -- Direct dependencies
  if !directDeps.isEmpty then
    h.putStr " ;\n  mer:directlyDependsOn "
    let mut first := true
    for d in directDeps do
      if first then first := false else h.putStr " , "
      h.putStr (declIri env d)
      trips := trips + 1

  -- Axiom usage
  if !axiomDeps.isEmpty then
    h.putStr " ;\n  mer:usesAxiom "
    let mut first := true
    for d in axiomDeps do
      if first then first := false else h.putStr " , "
      h.putStr (declIri env d)
      trips := trips + 1

  h.putStr " .\n"
  return trips

/-- Emit module-name triples for every distinct module referenced in `seen`. -/
private def emitModules (h : IO.FS.Handle) (seen : NameSet) : IO Nat := do
  let mut trips : Nat := 0
  for m in seen.toList do
    h.putStr s!"{moduleIri m} a mer:Module ;\n"
    h.putStr s!"  mer:moduleName \"{escapeLiteral (nameToDotted m)}\" .\n"
    trips := trips + 2
  return trips

/-- Decide whether a constant should be included in the dump. Excludes
    Lean-internal names (e.g. `_aux_`, `_eqRec_*`) but keeps everything else,
    including imported Mathlib declarations. -/
private def includeConst (name : Name) : Bool :=
  !name.isInternal

/-! ## Commands -/

/-- `#export_rdf "path/to/out.ttl"` — dump the entire current environment to a
    Turtle file aligned to the Meridian ontology. Streams to disk so that the
    full Mathlib4 corpus (~300k constants) does not blow up memory. -/
elab "#export_rdf " path:str : command => do
  let env ← getEnv
  let h ← IO.FS.Handle.mk path.getString .write
  h.putStr prologue
  let mut declCount : Nat := 0
  let mut tripleCount : Nat := 0
  let mut modules : NameSet := {}
  for (name, info) in env.constants.toList do
    if !includeConst name then continue
    let n ← liftIO (emitDecl h env name info)
    tripleCount := tripleCount + n
    declCount := declCount + 1
    match moduleOf? env name with
    | some m => modules := modules.insert m
    | none   => pure ()
  let modTrips ← liftIO (emitModules h modules)
  tripleCount := tripleCount + modTrips
  logInfo m!"wrote {declCount} declarations across {modules.size} modules ({tripleCount} triples) to {path.getString}"

/-- `#export_rdf_local "path/to/out.ttl"` — dump only declarations defined in
    the current module. Useful for testing and small per-project graphs. -/
elab "#export_rdf_local " path:str : command => do
  let env ← getEnv
  let h ← IO.FS.Handle.mk path.getString .write
  h.putStr prologue
  let mut declCount : Nat := 0
  let mut tripleCount : Nat := 0
  let mut modules : NameSet := {}
  for (name, info) in env.constants.toList do
    if !includeConst name then continue
    if env.getModuleIdxFor? name |>.isSome then continue
    let n ← liftIO (emitDecl h env name info)
    tripleCount := tripleCount + n
    declCount := declCount + 1
    match moduleOf? env name with
    | some m => modules := modules.insert m
    | none   => pure ()
  let modTrips ← liftIO (emitModules h modules)
  tripleCount := tripleCount + modTrips
  logInfo m!"wrote {declCount} declarations across {modules.size} modules ({tripleCount} triples) to {path.getString}"

end Meridian.Core.ExportRdf
