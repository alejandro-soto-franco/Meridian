# Meridian Ontology

A minimal OWL vocabulary for representing Lean 4 declaration knowledge graphs as RDF. Designed for export by [`Meridian.Core.ExportRdf`](../Meridian/Core/ExportRdf.lean) and direct loading into any SPARQL-capable triple store (Apache Jena Fuseki, Stardog, GraphDB, AWS Neptune, Blazegraph, rdflib).

| File | Purpose |
|------|---------|
| `meridian.ttl` | The ontology itself: classes, object properties, datatype properties. |
| `meridian-shapes.ttl` | SHACL shapes for structural validation of dumps. |

## Namespace

```
@prefix mer: <https://meridian.sotofranco.dev/ontology#> .
```

## Class hierarchy

```
                    mer:Declaration
                          │
        ┌────────┬────────┼────────┬─────────┬──────────┬─────────┐
        │        │        │        │         │          │         │
   mer:Theorem  mer:Def. mer:Axiom mer:Ind. mer:Ctor mer:Recursor mer:OpaqueDef

   mer:Module      (separate hierarchy — Lean source modules)
   mer:Dump        (separate — self-describing dump metadata)
```

| Class | Lean concept | `ConstantInfo` constructor |
|-------|--------------|----------------------------|
| `mer:Theorem` | Proven proposition | `.thmInfo` |
| `mer:Definition` | Definitional declaration | `.defnInfo` |
| `mer:Axiom` | Axiom or quotient primitive | `.axiomInfo`, `.quotInfo` |
| `mer:Inductive` | Inductive type | `.inductInfo` |
| `mer:Constructor` | Constructor of an inductive | `.ctorInfo` |
| `mer:Recursor` | Recursor of an inductive | `.recInfo` |
| `mer:OpaqueDef` | Opaque definition | `.opaqueInfo` |
| `mer:Module` | Lean source module | (file-level) |
| `mer:Dump` | Self-describing dump metadata | (synthetic) |

## Object properties

| Property | Domain | Range | Notes |
|----------|--------|-------|-------|
| `mer:directlyDependsOn` | `Declaration` | `Declaration` | Subject's type or value mentions the object as `Expr.const` (or `.proj` structure name). |
| `mer:dependsOn` | `Declaration` | `Declaration` | Transitive closure of `directlyDependsOn`. Reasoner-derived; not asserted by the emitter. |
| `mer:usesAxiom` | `Declaration` | `Axiom` | Subject directly references the object and the object is classified `mer:Axiom`. |
| `mer:inModule` | `Declaration` | `Module` | The Lean source module containing the declaration. |

## Datatype properties

| Property | Domain | Range | Notes |
|----------|--------|-------|-------|
| `mer:declName` | `Declaration` | `xsd:string` | Fully qualified Lean name (e.g. `Mathlib.Topology.Basic.Continuous`). |
| `mer:inNamespace` | `Declaration` | `xsd:string` | Dotted Lean namespace (the prefix of the name). |
| `mer:hasSorry` | `Declaration` | `xsd:boolean` | True iff the value transitively contains `sorryAx`. |
| `mer:sorryCount` | `Declaration` | `xsd:nonNegativeInteger` | Distinct `sorryAx` occurrences in the value. Omitted if zero. |
| `mer:typeSize` | `Declaration` | `xsd:nonNegativeInteger` | Subexpression count of the type. Cheap complexity proxy. |
| `mer:moduleName` | `Module` | `xsd:string` | Dotted Lean module name. |
| `mer:declCount` | `Dump` | `xsd:nonNegativeInteger` | Total declarations in the dump. |
| `mer:moduleCount` | `Dump` | `xsd:nonNegativeInteger` | Total distinct modules. |

## IRI scheme

```
https://meridian.sotofranco.dev/lean/<module-path-with-slashes>#<percent-encoded-name>
```

Examples:

| Lean | IRI |
|------|-----|
| `Mathlib.Topology.Basic.Continuous` | `https://meridian.sotofranco.dev/lean/Mathlib/Topology/Basic#Continuous` |
| `Init.Prelude.Eq` | `https://meridian.sotofranco.dev/lean/Init/Prelude#Eq` |
| `Foo.«hard name»` (current module) | `https://meridian.sotofranco.dev/lean/_local#Foo.hard%20name` |

Module IRIs drop the fragment:

```
https://meridian.sotofranco.dev/lean/Mathlib/Topology/Basic
```

The synthetic dump-metadata IRI is fixed:

```
https://meridian.sotofranco.dev/lean/_dump
```

Module dots become slashes; characters outside `[A-Za-z0-9_.~/-]` are percent-encoded as their UTF-8 bytes. Lean's syntactic `«»` brackets are stripped before encoding (they are not part of the canonical name).

## Alignment notes

The ontology is intentionally minimal and **not yet aligned** to upper or domain ontologies. Three plausible alignments for future revisions:

- **OMDoc** ([omdoc.org](https://omdoc.org/)) — XML-based mathematical knowledge representation. `mer:Theorem` ≈ `omdoc:Theorem`, `mer:Definition` ≈ `omdoc:Definition`. Different serialization, similar semantics.
- **MMT** ([uniformal.github.io](https://uniformal.github.io/)) — module system for mathematical theories. `mer:Module` would map to `mmt:Theory`.
- **PROV-O** ([w3.org/TR/prov-o](https://www.w3.org/TR/prov-o/)) — provenance vocabulary. `mer:Dump` could become a `prov:Entity`, with `prov:wasGeneratedBy` linking to the export run.

Pull requests adding alignment statements (`owl:equivalentClass`, `owl:equivalentProperty`) are welcome.

## SHACL validation

`meridian-shapes.ttl` enforces structural constraints:

- Every `mer:Declaration` has exactly one `mer:declName`, `mer:hasSorry`, and `mer:typeSize`.
- `mer:directlyDependsOn` ranges over `mer:Declaration`.
- `mer:usesAxiom` ranges over `mer:Axiom`.
- `mer:inModule` ranges over `mer:Module` and is single-valued.
- Every `mer:Module` has exactly one `mer:moduleName`.

Validate a dump against the shapes:

```bash
uv run --with pyshacl --with rdflib pyshacl \
  -s Ontology/meridian-shapes.ttl \
  -e Ontology/meridian.ttl \
  out/mathlib.ttl
```

`scripts/validate-dump.py` invokes pyshacl automatically when the `--shacl` flag is passed.

## License

The ontology is released under Apache 2.0 with the rest of Meridian. Use it freely in your own dumps or extend it; please retain attribution if you redistribute the file.
