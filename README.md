# Meridian

Open-source Lean 4 metaprogramming toolkit for mathematical formalisation. Proof search, sorry extraction, dependency analysis, Mathlib coverage reports, and domain-specific PDE tactics. Runs locally, no network calls, no data leaves your machine.

## Installation

Add to your `lakefile.toml`:

```toml
[[require]]
name = "Meridian"
git = "https://github.com/alejandro-soto-franco/Meridian"
rev = "main"
```

Then `lake update && lake build`.

## Modules

| Import | What you get |
|--------|-------------|
| `import Meridian.Core` | Sorry extraction, dependency graph, theorem extraction, verify, structural transforms, counterexample search |
| `import Meridian.Search` | Tactic suggestion, IDA* proof search, goal decomposition, type-class instance debugging |
| `import Meridian.Analysis` | Mathlib coverage analysis, project-level gap reports |
| `import Meridian.Domain.PDE` | Distributional derivative tactics, Sobolev exponent arithmetic, Biot-Savart connection automation, curvature bound tactics |
| `import Meridian.Domain.GMT` | Geometric measure theory: countably rectifiable sets, varifolds, first variation, stationary varifolds, interior monotonicity (statement-level) |
| `import Meridian` | Everything |

## Core Commands

```lean
-- Extract all sorries into standalone lemma stubs
#sorry_extract

-- Build dependency graph (outputs DOT format)
#dep_graph

-- Sorry inventory with auto-categorisation
#sorry_inventory

-- Extract theorems with metadata
#extract_theorems

-- Verify a candidate proof against a sorry
#verify_proof declName

-- Structural transforms
#theorem2sorry
#normalize
#rename oldName newName

-- Counterexample search
#disprove declName
```

## Search Tactics

```lean
-- Suggest tactics for the current goal
meridian_suggest

-- Multi-step proof search (IDA* with memoization)
meridian_search (heartbeats := 400000)

-- Decompose goal into sub-lemmas
meridian_decompose

-- Diagnose type-class synthesis failure
#instance_debug SomeTypeClass
```

## Analysis Commands

```lean
-- Find near-miss Mathlib lemmas for a sorry
#mathlib_coverage declName

-- Project-level gap report
#gap_report
```

## RDF / SPARQL Export

Meridian can dump the entire current Lean environment to a Turtle (`.ttl`) file aligned to the [Meridian ontology](Ontology/meridian.ttl) ([overview](Ontology/README.md), [SHACL shapes](Ontology/meridian-shapes.ttl)). The dump is a knowledge graph: nodes are declarations (theorems, definitions, axioms, inductives, constructors, recursors, opaque defs), edges are direct dependencies and axiom usages. Output is suitable for loading into Apache Jena Fuseki, Stardog, GraphDB, AWS Neptune, Blazegraph, or any SPARQL-capable triple store.

```lean
-- Dump the entire environment (every imported constant included)
#export_rdf "out/mathlib.ttl"

-- Dump only declarations defined in the current module
#export_rdf_local "out/local.ttl"
```

The driver `Drivers/ExportMathlib.lean` imports `Mathlib` and emits the full corpus. Convenience targets ship in the `Makefile`:

```bash
make export-mathlib   # dump out/mathlib.ttl + .sha256
make validate         # rdflib parse + class counts + 5 SPARQL queries
make validate-shacl   # additionally run pyshacl against Ontology/meridian-shapes.ttl
make release          # gzip + manifest, ready for `gh release create`
```

The IRI scheme is `https://meridian.sotofranco.dev/lean/<module-path>#<decl-name>`, with module dots converted to slashes. A declaration in `Mathlib.Topology.Basic` named `Continuous` gets the IRI `<https://meridian.sotofranco.dev/lean/Mathlib/Topology/Basic#Continuous>`. See [Ontology/README.md](Ontology/README.md) for the full IRI scheme, class hierarchy, and property tables.

### Loading into a SPARQL endpoint

```bash
./scripts/load-fuseki.sh out/mathlib.ttl
# Fuseki listening on http://localhost:3030/meridian/sparql
```

### Example queries

The `examples/sparql/` directory ships five queries:

| File | Question |
|------|----------|
| `01-namespace-counts.sparql` | Top namespaces by declaration count |
| `02-sorries-with-downstream.sparql` | Sorry-bearing declarations ranked by direct downstream impact |
| `03-axiom-usage-census.sparql` | Which axioms are used and by how many declarations |
| `04-direct-dependents-of.sparql` | All declarations directly depending on a chosen target |
| `05-complexity-distribution.sparql` | Histogram of theorem type-size buckets |

The queries are reasoning-agnostic — they use `rdfs:subClassOf*` property paths so they work whether or not the store materialises subclass inferences. For best results, load `Ontology/meridian.ttl` into the same dataset as the dump.

Run any of them against the loaded endpoint:

```bash
curl -fsS -H 'Accept: application/sparql-results+json' \
  --data-urlencode "query=$(cat examples/sparql/01-namespace-counts.sparql)" \
  http://localhost:3030/meridian/sparql | jq .
```

### Validation

`scripts/validate-dump.py` runs three layers of validation against any dump:

1. Turtle parses cleanly via [rdflib](https://rdflib.readthedocs.io/).
2. Class counts (theorems / definitions / axioms / inductives / constructors / recursors / opaques / modules / sorry-bearing).
3. Conformance check: every IRI referenced via `mer:directlyDependsOn`, `mer:usesAxiom`, or `mer:inModule` is itself typed in the graph (orphans expected only on module-local dumps).
4. All five example SPARQL queries succeed and return rows.
5. *(Optional, with `--shacl`)* SHACL validation against `Ontology/meridian-shapes.ttl` via [pyshacl](https://github.com/RDFLib/pySHACL).

```bash
uv run --quiet --with rdflib scripts/validate-dump.py out/mathlib.ttl
uv run --quiet --with rdflib --with pyshacl scripts/validate-dump.py --shacl out/mathlib.ttl
```

## Domain Tactics (PDE)

```lean
-- Distributional derivative / weak formulation
meridian_distrib

-- Sobolev exponent arithmetic
meridian_sobolev

-- Biot-Savart connection automation
meridian_biot_savart
meridian_connection

-- Curvature and helicity
meridian_curvature
meridian_helicity
```

## Domain Tactics (GMT)

```lean
-- Geometric measure theory objects (v0.1: definitions + statement-level theorems)
open Meridian.Domain.GMT
-- CountablyRectifiable k S, Varifold E k, firstVariation, IsStationary,
-- densityRatio, monotonicity_of_stationary
```

## License

Apache 2.0. Copyright 2026 Alejandro Jose Soto Franco.

## Design

Meridian runs entirely on your machine. No network calls, no hosted API, no third-party servers. Your proof code stays local.
