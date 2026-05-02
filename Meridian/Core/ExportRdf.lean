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

/-! ## Buffered writer

`IO.FS.Handle.putStr` issues one syscall per call. Emitting ~300k declarations
with ~50 short writes each is millions of syscalls, which dominates wall
time. `Buf` accumulates into an `IO.Ref String` and flushes at a tunable
byte threshold (~64 KiB), reducing syscall count by ~3 orders of magnitude. -/

private structure Buf where
  ref       : IO.Ref String
  handle    : IO.FS.Handle
  threshold : Nat

private def Buf.create (h : IO.FS.Handle) (threshold : Nat := 65536) : IO Buf := do
  let r ← IO.mkRef ""
  return { ref := r, handle := h, threshold := threshold }

private def Buf.write (b : Buf) (s : String) : IO Unit := do
  b.ref.modify (· ++ s)
  let cur ← b.ref.get
  if cur.length ≥ b.threshold then
    b.handle.putStr cur
    b.ref.set ""

private def Buf.flush (b : Buf) : IO Unit := do
  let cur ← b.ref.get
  if !cur.isEmpty then
    b.handle.putStr cur
    b.ref.set ""

/-! ## IRI construction -/

/-- Percent-encode bytes outside the conservative URL-safe set. We keep
    `A-Z a-z 0-9 - _ . ~ /` and `#` (since `#` is the fragment separator we
    deliberately emit). Everything else becomes `%HH`. Handles arbitrary
    Unicode codepoints (French quotes, mathematical operators, etc.) by
    encoding their UTF-8 byte sequence. -/
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

/-- IRI of the synthetic dump-metadata subject. -/
private def dumpMetaIri : String :=
  "<https://meridian.sotofranco.dev/lean/_dump>"

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

/-! ## Equation-compiler bloat filter -/

/-- True if the last component of `n` matches a pattern that the Lean
    equation compiler or codegen emits as a derived helper, not a
    user-declared entity. We keep `Name.isInternal` (covers `_aux_*`, leading
    underscore) and add the patterns that escape it. Conservative: only
    skip names that have no semantic content for downstream KG consumers. -/
private def isDerivedHelper (n : Name) : Bool :=
  match n with
  | .str _ s =>
    s == "inj" || s == "injEq" || s == "noConfusionType" || s == "noConfusion"
    || s == "rec" || s == "recOn" || s == "casesOn" || s == "below" || s == "ibelow"
    || s == "brecOn" || s == "binductionOn" || s == "ndrec" || s == "ndrecOn"
    || s == "sizeOf" || s == "_sizeOf_1" || s == "_sizeOf_inst"
    || s.startsWith "proof_" || s.startsWith "match_" || s.startsWith "_eq_"
    || s.startsWith "eq_" && (s.drop 3).all Char.isDigit
    || s.startsWith "_proof_" || s.startsWith "_match_"
    || s.startsWith "_cstage" || s.startsWith "_sunfold"
    || s.startsWith "_unsafe_rec"
  | _ => false

/-- Combined inclusion filter: skip Lean-internal names and equation-compiler
    artefacts. -/
private def includeConst (env : Environment) (name : Name) : Bool :=
  if name.isInternal then false
  else if isDerivedHelper name then false
  else
    -- Drop `Foo.proof_N` style trailing-numeric helpers that escape the
    -- pattern check above (some Mathlib generators produce these).
    match env.find? name with
    | some _ => true
    | none   => false

/-! ## Dependency collection (extended) -/

/-- Extension of `Meridian.Core.SorryExtract.collectDeps` that also includes
    the structure name of each `.proj` node. The base version drops it. -/
private partial def collectDepsExt (e : Expr) : NameSet :=
  go e {}
where
  go : Expr → NameSet → NameSet
  | .const n _,        acc => acc.insert n
  | .app f a,          acc => go a (go f acc)
  | .lam _ d b _,      acc => go b (go d acc)
  | .forallE _ d b _,  acc => go b (go d acc)
  | .letE _ t v b _,   acc => go b (go v (go t acc))
  | .mdata _ e,        acc => go e acc
  | .proj sn _ e,      acc => go e (acc.insert sn)
  | _,                 acc => acc

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
  "@prefix xsd:  <http://www.w3.org/2001/XMLSchema#> .\n" ++
  "@prefix dct:  <http://purl.org/dc/terms/> .\n\n"

/-- Emit a graph-level metadata block describing the dump itself. -/
private def emitDumpMeta (b : Buf) (declCount moduleCount : Nat) : IO Nat := do
  b.write s!"{dumpMetaIri} a mer:Dump ;\n"
  b.write s!"  dct:source \"Lean {Lean.versionString}\" ;\n"
  b.write s!"  mer:declCount \"{declCount}\"^^xsd:nonNegativeInteger ;\n"
  b.write s!"  mer:moduleCount \"{moduleCount}\"^^xsd:nonNegativeInteger .\n\n"
  return 4

/-- Build the full Turtle block for a single declaration as a single string.
    Returns the string and the triple count. Single-string-then-write keeps
    syscalls per declaration to one buffered append. -/
private def renderDecl (env : Environment) (name : Name) (info : ConstantInfo)
    : String × Nat := Id.run do
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

  let typeDeps := collectDepsExt info.type
  let valDeps := match info.value? with
    | some v => collectDepsExt v
    | none   => {}
  let directDeps : List Name :=
    (typeDeps.merge valDeps).toList
      |>.filter (fun n => !n.isInternal && n != name)

  let axiomDeps : List Name := directDeps.filter fun n =>
    match env.find? n with
    | some ci => isAxiomLike ci
    | none    => false

  let mut s := s!"{subj} a {cls} ;\n"
  let mut trips : Nat := 1
  s := s ++ s!"  mer:declName \"{escapeLiteral fullName}\" ;\n"
  trips := trips + 1
  if !ns.isEmpty then
    s := s ++ s!"  mer:inNamespace \"{escapeLiteral ns}\" ;\n"
    trips := trips + 1
  s := s ++ s!"  mer:hasSorry \"{if hasS then "true" else "false"}\"^^xsd:boolean ;\n"
  trips := trips + 1
  if sorryCount > 0 then
    s := s ++ s!"  mer:sorryCount \"{sorryCount}\"^^xsd:nonNegativeInteger ;\n"
    trips := trips + 1
  s := s ++ s!"  mer:typeSize \"{tSize}\"^^xsd:nonNegativeInteger"
  trips := trips + 1
  match moduleOf? env name with
  | some m =>
    s := s ++ s!" ;\n  mer:inModule {moduleIri m}"
    trips := trips + 1
  | none => pure ()
  if !directDeps.isEmpty then
    s := s ++ " ;\n  mer:directlyDependsOn "
    let mut first := true
    for d in directDeps do
      if first then
        first := false
        s := s ++ declIri env d
      else
        s := s ++ " , " ++ declIri env d
      trips := trips + 1
  if !axiomDeps.isEmpty then
    s := s ++ " ;\n  mer:usesAxiom "
    let mut first := true
    for d in axiomDeps do
      if first then
        first := false
        s := s ++ declIri env d
      else
        s := s ++ " , " ++ declIri env d
      trips := trips + 1
  s := s ++ " .\n"
  return (s, trips)

/-- Emit module-name triples for every distinct module referenced in `seen`. -/
private def emitModules (b : Buf) (seen : NameSet) : IO Nat := do
  let mut trips : Nat := 0
  for m in seen.toList do
    b.write s!"{moduleIri m} a mer:Module ;\n"
    b.write s!"  mer:moduleName \"{escapeLiteral (nameToDotted m)}\" .\n"
    trips := trips + 2
  return trips

/-- Core dump routine: walk every constant matching `keep`, render, write. -/
private def runDump (path : String) (keep : Environment → Name → ConstantInfo → Bool)
    : CommandElabM (Nat × Nat × Nat) := do
  let env ← getEnv
  let h ← liftM (m := IO) (IO.FS.Handle.mk path .write)
  let buf ← liftM (m := IO) (Buf.create h)
  liftM (m := IO) (buf.write prologue)
  let mut declCount : Nat := 0
  let mut tripleCount : Nat := 0
  let mut modules : NameSet := {}
  -- Walk map₂ (imported) first, then map₁ (current module). map₂ is a
  -- HashMap-flavour structure with a foldM that doesn't require materialising
  -- a List, which matters at 300k+ entries.
  let walk (acc : Nat × Nat × NameSet) (name : Name) (info : ConstantInfo)
      : IO (Nat × Nat × NameSet) := do
    let (dc, tc, mods) := acc
    if !keep env name info then return (dc, tc, mods)
    let (s, n) := renderDecl env name info
    buf.write s
    let mods' := match moduleOf? env name with
      | some m => mods.insert m
      | none   => mods
    return (dc + 1, tc + n, mods')
  let acc0 : Nat × Nat × NameSet := (declCount, tripleCount, modules)
  let acc1 ← liftM (m := IO) <| env.constants.map₂.foldlM (init := acc0) walk
  let acc2 ← liftM (m := IO) <| env.constants.map₁.foldM (init := acc1) walk
  let (dc, tc, mods) := acc2
  declCount := dc; tripleCount := tc; modules := mods
  let modTrips ← liftM (m := IO) (emitModules buf modules)
  tripleCount := tripleCount + modTrips
  let metaTrips ← liftM (m := IO) (emitDumpMeta buf declCount modules.size)
  tripleCount := tripleCount + metaTrips
  liftM (m := IO) buf.flush
  liftM (m := IO) h.flush
  return (declCount, modules.size, tripleCount)

/-! ## Commands -/

/-- `#export_rdf "path/to/out.ttl"` — dump the entire current environment to a
    Turtle file aligned to the Meridian ontology. Streams to disk in 64 KiB
    chunks so the full Mathlib4 corpus (~300k constants) does not blow up
    memory. -/
elab "#export_rdf " path:str : command => do
  let (decls, mods, trips) ← runDump path.getString (fun env n _ => includeConst env n)
  logInfo m!"wrote {decls} declarations across {mods} modules ({trips} triples) to {path.getString}"

/-- `#export_rdf_local "path/to/out.ttl"` — dump only declarations defined in
    the current module. Useful for testing and small per-project graphs. -/
elab "#export_rdf_local " path:str : command => do
  let keep (env : Environment) (n : Name) (_ : ConstantInfo) : Bool :=
    includeConst env n && (env.getModuleIdxFor? n).isNone
  let (decls, mods, trips) ← runDump path.getString keep
  logInfo m!"wrote {decls} declarations across {mods} modules ({trips} triples) to {path.getString}"

end Meridian.Core.ExportRdf
