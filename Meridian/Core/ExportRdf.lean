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

/-! ## Writer

We write directly to `IO.FS.Handle` rather than maintaining an in-Lean
buffer. Lean's `Handle.putStr` is backed by libc `fwrite`, which already
block-buffers at 4 KiB. Adding an in-Lean buffer on top of that requires
either O(N²) string concatenation (the trap that made the first dump
attempt take ~21 hours on Mathlib) or careful pre-sized ByteArray
arithmetic — both unnecessary when libc handles the batching for us.

The thin `Buf` wrapper is kept so render code stays handle-agnostic and so
we can later swap in a smarter writer (e.g. async, gzip-on-the-fly). -/

private structure Buf where
  handle : IO.FS.Handle

private def Buf.create (h : IO.FS.Handle) : IO Buf := do
  return { handle := h }

private def Buf.write (b : Buf) (s : String) : IO Unit :=
  b.handle.putStr s

private def Buf.flush (b : Buf) : IO Unit :=
  b.handle.flush

/-! ## IRI construction -/

/-- Percent-encode bytes outside the conservative URL-safe set, keeping `#`
    in the safe set (suitable for path segments where `#` is the IRI fragment
    separator). Used for the module path portion of a decl IRI. -/
private def percentEncodeKeepHash (s : String) : String :=
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

/-- Percent-encode bytes for the fragment portion of an IRI. Unlike
    `percentEncodeKeepHash`, `#` is NOT in the safe set — a Lean name
    containing `#` (e.g. `command#redundant_imports`) encodes to `%23` so
    the resulting IRI has exactly one `#` (the module-vs-name boundary). -/
private def percentEncodeFragment (s : String) : String :=
  let safe (c : Char) : Bool :=
    c.isAlphanum || c == '-' || c == '_' || c == '.' || c == '~'
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

/-- True when declaration `n`'s defining module has one of `scope`'s names as its
    root component, or when `scope` is empty (no restriction). Drives
    `export-meridian --scope <Prefix>`: keep only a project's own declarations
    (e.g. `EllipticDirichlet`, `DeGiorgi`) while still emitting their dependency
    edges, whose out-of-scope (Mathlib) targets resolve against the shared Mathlib
    graph in the unified store. A declaration with no defining module (a local of
    the current module) is out of scope under a non-empty `scope`. -/
def moduleInScope (env : Environment) (scope : Array Name) (n : Name) : Bool :=
  scope.isEmpty ||
    match moduleOf? env n with
    | some m => scope.contains m.getRoot
    | none   => false

/-- Build the IRI of a declaration. v0.2: path segment keeps `#` (none in
    practice; `/` is the only special char), fragment percent-encodes `#`
    so Lean names like `command#redundant_imports` produce one valid
    `#`-separated IRI rather than the malformed double-`#` form. -/
private def declIri (env : Environment) (declName : Name) : String :=
  let modSlug := match moduleOf? env declName with
    | some m => modulePath m
    | none   => "_local"
  let path := percentEncodeKeepHash modSlug
  let frag := percentEncodeFragment (nameToDotted declName)
  s!"<https://meridian.sotofranco.dev/lean/{path}#{frag}>"

/-- Build the IRI of a module. -/
private def moduleIri (modName : Name) : String :=
  let slug := percentEncodeKeepHash (modulePath modName)
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
    artefacts. Public so the `lake exe export-meridian` driver
    (`Meridian.Drivers.ExportMain`) can share the same filter as the
    `#export_rdf` editor commands. -/
def includeConst (env : Environment) (name : Name) : Bool :=
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
    the structure name of each `.proj` node. The base version drops it.

    Carries an `ExprSet` visited-set so shared subterms of the hash-consed `Expr`
    DAG are walked once; the previous naive recursion revisited them and was
    exponential (the bottleneck in the full-Mathlib export). Core's
    `getUsedConstantsAsSet` is not reused here because it does not surface the
    `.proj` structure name. -/
private partial def collectDepsExt (e : Expr) : NameSet :=
  (go e ({}, ({} : ExprSet))).1
where
  go (e : Expr) (acc : NameSet × ExprSet) : NameSet × ExprSet :=
    let (deps, seen) := acc
    if seen.contains e then (deps, seen)
    else
      let acc := (deps, seen.insert e)
      match e with
      | .const n _        => (acc.1.insert n, acc.2)
      | .app f a          => go a (go f acc)
      | .lam _ d b _      => go b (go d acc)
      | .forallE _ d b _  => go b (go d acc)
      | .letE _ t v b _   => go b (go v (go t acc))
      | .mdata _ e        => go e acc
      | .proj sn _ e      => let (d, s) := go e acc; (d.insert sn, s)
      | _                 => acc

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
  "@prefix owl:  <http://www.w3.org/2002/07/owl#> .\n" ++
  "@prefix xsd:  <http://www.w3.org/2001/XMLSchema#> .\n" ++
  "@prefix dct:  <http://purl.org/dc/terms/> .\n\n" ++
  "<https://meridian.sotofranco.dev/ontology> owl:versionInfo \"0.2.0\" .\n\n"

/-- Emit a graph-level metadata block describing the dump itself. -/
private def emitDumpMeta (b : Buf) (declCount moduleCount : Nat) : IO Nat := do
  b.write s!"{dumpMetaIri} a mer:Dump ;\n"
  b.write s!"  dct:source \"Lean {Lean.versionString}\" ;\n"
  b.write s!"  mer:declCount \"{declCount}\"^^xsd:nonNegativeInteger ;\n"
  b.write s!"  mer:moduleCount \"{moduleCount}\"^^xsd:nonNegativeInteger .\n\n"
  return 4

/-- Emit the v0.2 completion sentinel as the very last triple. Consumers
    treat its absence as proof of a truncated/crashed dump. -/
private def emitSentinel (b : Buf) : IO Nat := do
  b.write "<urn:meridian:dump> mer:complete \"true\"^^xsd:boolean .\n"
  return 1

/-- Write the Turtle block for a single declaration directly to the buffer.
    Returns the triple count. Writing piece-by-piece avoids the O(K²)
    string-build that arises from `s := s ++ ...` over K dep IRIs (Lean's
    `String ++` is O(|s|), so a per-decl single-string build is quadratic
    in the dep count and dominates wallclock at Mathlib scale). -/
private def renderDecl (b : Buf) (env : Environment) (name : Name)
    (info : ConstantInfo) : IO Nat := do
  let subj := declIri env name
  let cls  := classOf info
  let ns   := nameToDotted name.getPrefix
  let fullName := nameToDotted name
  let tSize := exprSize info.type

  let typeDeps := collectDepsExt info.type
  let valDeps := match info.value? with
    | some v => collectDepsExt v
    | none   => {}
  -- `sorryAx` is a constant, so its membership in the value's dep set is exactly
  -- `containsSorry value`; reuse `valDeps` rather than a second full Expr walk.
  let hasS := valDeps.contains ``sorryAx
  -- Only walk for sorry goals when a sorry is actually present (≈never across
  -- Mathlib), sparing every proved declaration a redundant traversal.
  let sorryCount := if hasS then
      match info.value? with
      | some v => (collectSorryGoals v).length
      | none   => 0
    else 0
  let directDeps : List Name :=
    (typeDeps.merge valDeps).toList
      |>.filter (fun n => !n.isInternal && n != name)

  let axiomDeps : List Name := directDeps.filter fun n =>
    match env.find? n with
    | some ci => isAxiomLike ci
    | none    => false

  let mut trips : Nat := 0
  b.write s!"{subj} a {cls} ;\n"; trips := trips + 1
  b.write s!"  mer:declName \"{escapeLiteral fullName}\" ;\n"; trips := trips + 1
  if !ns.isEmpty then
    b.write s!"  mer:inNamespace \"{escapeLiteral ns}\" ;\n"; trips := trips + 1
  b.write s!"  mer:hasSorry \"{if hasS then "true" else "false"}\"^^xsd:boolean ;\n"
  trips := trips + 1
  if sorryCount > 0 then
    b.write s!"  mer:sorryCount \"{sorryCount}\"^^xsd:nonNegativeInteger ;\n"
    trips := trips + 1
  b.write s!"  mer:typeSize \"{tSize}\"^^xsd:nonNegativeInteger"
  trips := trips + 1
  -- v0.2: emit mer:sourceLoc when the environment has a recorded range.
  -- `declRangeExt.find?` is pure — same lookup `findDeclarationRangesCore?`
  -- performs in MonadEnv contexts, but callable directly from IO since we
  -- already hold `env`. Built-in / internal decls without ranges are
  -- skipped (predicate is optional per v0.2 ontology).
  let ranges? :=
    declRangeExt.find? (level := .exported) env name <|>
    declRangeExt.find? (level := .server)   env name
  if let some ranges := ranges? then
    let p := ranges.range.pos
    let modPath := match moduleOf? env name with
      | some m => modulePath m ++ ".lean"
      | none   => "_local.lean"
    let fileLineCol := s!"{modPath}:{p.line}:{p.column}"
    b.write s!" ;\n  mer:sourceLoc \"{escapeLiteral fileLineCol}\""
    trips := trips + 1
  -- v0.2: emit mer:docstring when the environment carries one for this decl.
  -- `docStringExt` is the env extension that registers raw `/-- ... -/`
  -- comment bodies; absent for built-ins and for decls written without
  -- docstrings. Pure lookup on the Environment, mirroring P1.2's
  -- `declRangeExt.find?` pattern — no monadic enrichment, no alias
  -- resolution, no markdown normalisation (raw body per v0.2 spec).
  if let some doc := docStringExt.find? (level := .server) env name then
    b.write s!" ;\n  mer:docstring \"{escapeLiteral doc}\""
    trips := trips + 1
  -- v0.2: emit mer:typeSignature with a stringified Lean type expression.
  -- Uses `Expr.dbgToString` (the `ToString Expr` instance), which is pure
  -- on `Expr` — no MetaM threading needed, keeping `renderDecl` in IO with
  -- the same monad discipline as the sourceLoc / docstring blocks above.
  -- Output is the debug/desugared form (e.g. `GT.gt.{0} Nat instLTNat …`
  -- rather than `_ > _`); `Lean.PrettyPrinter.ppExpr` would yield the
  -- prettier surface form but requires MetaM and would force a structural
  -- rewrite of the walk loop. Capped at 8192 chars to prevent Mathlib's
  -- deepest universe-polymorphic types from blowing up dump size;
  -- consumers fall back to mer:typeSize for size-bound queries.
  let typeSig := Expr.dbgToString info.type
  if typeSig.length > 0 && typeSig.length ≤ 8192 then
    b.write s!" ;\n  mer:typeSignature \"{escapeLiteral typeSig}\""
    trips := trips + 1
  match moduleOf? env name with
  | some m =>
    b.write s!" ;\n  mer:inModule {moduleIri m}"
    trips := trips + 1
  | none => pure ()
  if !directDeps.isEmpty then
    b.write " ;\n  mer:directlyDependsOn "
    let mut first := true
    for d in directDeps do
      if first then first := false
      else b.write " , "
      b.write (declIri env d)
      trips := trips + 1
  if !axiomDeps.isEmpty then
    b.write " ;\n  mer:usesAxiom "
    let mut first := true
    for d in axiomDeps do
      if first then first := false
      else b.write " , "
      b.write (declIri env d)
      trips := trips + 1
  b.write " .\n"
  return trips

/-- Emit module-name triples for every distinct module referenced in `seen`. -/
private def emitModules (b : Buf) (seen : NameSet) : IO Nat := do
  let mut trips : Nat := 0
  for m in seen.toList do
    b.write s!"{moduleIri m} a mer:Module ;\n"
    b.write s!"  mer:moduleName \"{escapeLiteral (nameToDotted m)}\" .\n"
    trips := trips + 2
  return trips

/-- Pure-IO core dump routine: walks every constant matching `keep` over an
    explicit `Environment` and writes Turtle to `path`. Callable from any IO
    context (including `lake exe` `main`), so we can drive the dump from
    `Meridian.Drivers.ExportMain` after populating an Environment via
    `Lean.withImportModules`. The `CommandElabM`-flavoured `runDump` below is
    a thin wrapper that supplies `← getEnv`. -/
def runDumpIO (env : Environment) (path : String)
    (keep : Environment → Name → ConstantInfo → Bool) : IO (Nat × Nat × Nat) := do
  let h ← IO.FS.Handle.mk path .write
  let buf ← Buf.create h
  buf.write prologue
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
    let n ← renderDecl buf env name info
    let mods' := match moduleOf? env name with
      | some m => mods.insert m
      | none   => mods
    return (dc + 1, tc + n, mods')
  let acc0 : Nat × Nat × NameSet := (declCount, tripleCount, modules)
  let acc1 ← env.constants.map₂.foldlM (init := acc0) walk
  let acc2 ← env.constants.map₁.foldM (init := acc1) walk
  let (dc, tc, mods) := acc2
  declCount := dc; tripleCount := tc; modules := mods
  -- v0.2: emit modules + meta + completion sentinel inside a try so the
  -- finally block still flushes if any of them panics. The sentinel is the
  -- LAST triple; consumers detect its absence as a partial-dump warning.
  try
    let modTrips ← emitModules buf modules
    tripleCount := tripleCount + modTrips
    let metaTrips ← emitDumpMeta buf declCount modules.size
    tripleCount := tripleCount + metaTrips
    let sentinelTrips ← emitSentinel buf
    tripleCount := tripleCount + sentinelTrips
  finally
    buf.flush
    h.flush
  return (declCount, modules.size, tripleCount)

/-- Core dump routine, `CommandElabM` wrapper. Resolves the current
    environment via `getEnv` and delegates to `runDumpIO`, so editor commands
    (`#export_rdf`, `#export_rdf_local`) and the Lake exe driver share the
    same implementation. -/
private def runDump (path : String) (keep : Environment → Name → ConstantInfo → Bool)
    : CommandElabM (Nat × Nat × Nat) := do
  let env ← getEnv
  liftM (m := IO) (runDumpIO env path keep)

/-! ## Commands -/

/-- `#export_rdf "path/to/out.ttl"` — dump the entire current environment to a
    Turtle file aligned to the Meridian ontology. Writes are passed straight
    through to libc's block-buffered fwrite, so memory stays flat regardless
    of corpus size. -/
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

/-! ## Profiling

`#profile_deps "out/profile.csv"` walks the env once, timing the per-decl
hot path used by `#export_rdf` (`collectDepsExt` ×2 + `containsSorry` +
axiom-check filter). Rows are written for every declaration whose total
hot-path cost exceeds 50 ms. A top-20 summary is logged. Used to
diagnose pathological declarations whose Expr DAG triggers exponential
walks under naive recursion. -/

private def slowMsDefault : Nat := 50

/-- Single-decl hot-path measurement, in nanoseconds. -/
private structure DeclProfile where
  name        : Name
  typeSize    : Nat
  valueSize   : Nat
  typeDepsNs  : Nat
  valDepsNs   : Nat
  sorryNs     : Nat
  axiomNs     : Nat
  depCount    : Nat
  deriving Inhabited

private def DeclProfile.totalNs (p : DeclProfile) : Nat :=
  p.typeDepsNs + p.valDepsNs + p.sorryNs + p.axiomNs

private def fmtMs (ns : Nat) : String :=
  let ms := ns / 1000000
  let frac := (ns % 1000000) / 100000
  s!"{ms}.{frac}"

elab "#profile_deps " path:str : command => do
  let env ← getEnv
  let h ← liftM (m := IO) (IO.FS.Handle.mk path.getString .write)
  liftM (m := IO) <| h.putStr "name,type_size,value_size,type_deps_us,val_deps_us,sorry_us,axiom_us,dep_count,total_us\n"
  let slowNs := slowMsDefault * 1000000
  let walk (acc : Nat × Nat × Array DeclProfile) (name : Name) (info : ConstantInfo)
      : IO (Nat × Nat × Array DeclProfile) := do
    let (scanned, slowCount, top) := acc
    if !includeConst env name then return (scanned, slowCount, top)
    let tSize := exprSize info.type
    let vSize := match info.value? with | some v => exprSize v | none => 0
    let t0 ← IO.monoNanosNow
    let typeDeps := collectDepsExt info.type
    let t1 ← IO.monoNanosNow
    let valDeps := match info.value? with
      | some v => collectDepsExt v
      | none   => {}
    let t2 ← IO.monoNanosNow
    let _ := match info.value? with
      | some v => containsSorry v
      | none   => false
    let t3 ← IO.monoNanosNow
    let directDeps : List Name :=
      (typeDeps.merge valDeps).toList |>.filter (fun n => !n.isInternal && n != name)
    let _ := directDeps.filter fun n =>
      match env.find? n with
      | some ci => isAxiomLike ci
      | none    => false
    let t4 ← IO.monoNanosNow
    let p : DeclProfile :=
      { name := name, typeSize := tSize, valueSize := vSize
      , typeDepsNs := t1 - t0, valDepsNs := t2 - t1
      , sorryNs := t3 - t2, axiomNs := t4 - t3
      , depCount := directDeps.length }
    let total := p.totalNs
    let scanned' := scanned + 1
    let mut slowCount' := slowCount
    let mut top' := top
    if total ≥ slowNs then
      slowCount' := slowCount + 1
      h.putStr s!"{name},{p.typeSize},{p.valueSize},{p.typeDepsNs/1000},{p.valDepsNs/1000},{p.sorryNs/1000},{p.axiomNs/1000},{p.depCount},{total/1000}\n"
      top' := top.push p
    return (scanned', slowCount', top')
  let acc0 : Nat × Nat × Array DeclProfile := (0, 0, #[])
  let acc1 ← liftM (m := IO) <| env.constants.map₂.foldlM (init := acc0) walk
  let (scanned, slowCount, top) ← liftM (m := IO) <| env.constants.map₁.foldM (init := acc1) walk
  liftM (m := IO) h.flush
  -- Sort top profiles by total time (descending) and report top 20.
  let sorted := top.toList.mergeSort (fun a b => a.totalNs > b.totalNs)
  let topK := sorted.take 20
  let mut summary := s!"profile: scanned {scanned} decls, {slowCount} slow (≥{slowMsDefault}ms), CSV at {path.getString}\n"
  summary := summary ++ "top 20 by total hot-path time:\n"
  for (i, p) in topK.zip (List.range topK.length) do
    summary := summary ++ s!"  {p+1}. [{fmtMs i.totalNs}ms] {i.name}  type={i.typeSize} val={i.valueSize} deps={i.depCount} (typeDeps {fmtMs i.typeDepsNs}ms, valDeps {fmtMs i.valDepsNs}ms, sorry {fmtMs i.sorryNs}ms, axiom {fmtMs i.axiomNs}ms)\n"
  logInfo summary

end Meridian.Core.ExportRdf
