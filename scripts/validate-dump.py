#!/usr/bin/env python3
"""validate-dump.py — parse a Meridian Turtle dump with rdflib, run every
SPARQL query under examples/sparql/ against it, optionally validate against
the SHACL shapes, and check ontology conformance (every dependency target
exists in the graph).

Usage:
    uv run --with rdflib scripts/validate-dump.py out/mathlib.ttl
    uv run --with rdflib --with pyshacl scripts/validate-dump.py --shacl out/mathlib.ttl

Requires: rdflib (always), pyshacl (only when --shacl is passed).
"""

from __future__ import annotations

import argparse
import sys
import time
from pathlib import Path

import rdflib
from rdflib.namespace import RDF


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Validate a Meridian Turtle dump.")
    p.add_argument("dump", type=Path, help="Path to the .ttl dump.")
    p.add_argument("--shacl", action="store_true",
                   help="Run SHACL validation via pyshacl (slow on large dumps).")
    p.add_argument("--no-queries", action="store_true",
                   help="Skip running the example SPARQL queries.")
    p.add_argument("--max-orphans", type=int, default=10,
                   help="Number of dangling dep targets to print (default 10).")
    return p.parse_args()


def load_graph(path: Path, ontology: Path | None = None) -> rdflib.Graph:
    print(f"==> parsing {path}")
    t0 = time.monotonic()
    g = rdflib.Graph()
    g.parse(str(path), format="turtle")
    secs = time.monotonic() - t0
    print(f"    parsed {len(g):,} triples in {secs:.1f}s")
    if ontology and ontology.is_file():
        before = len(g)
        g.parse(str(ontology), format="turtle")
        added = len(g) - before
        print(f"    merged ontology ({ontology.name}): +{added:,} triples")
    return g


def class_counts(g: rdflib.Graph, mer: rdflib.Namespace) -> dict[str, int]:
    return {
        "Declaration":   sum(1 for _ in g.subject_objects(mer.declName)),
        "Theorem":       sum(1 for _ in g.subjects(RDF.type, mer.Theorem)),
        "Definition":    sum(1 for _ in g.subjects(RDF.type, mer.Definition)),
        "Axiom":         sum(1 for _ in g.subjects(RDF.type, mer.Axiom)),
        "Inductive":     sum(1 for _ in g.subjects(RDF.type, mer.Inductive)),
        "Constructor":   sum(1 for _ in g.subjects(RDF.type, mer.Constructor)),
        "Recursor":      sum(1 for _ in g.subjects(RDF.type, mer.Recursor)),
        "OpaqueDef":     sum(1 for _ in g.subjects(RDF.type, mer.OpaqueDef)),
        "Module":        sum(1 for _ in g.subjects(RDF.type, mer.Module)),
        "Dump":          sum(1 for _ in g.subjects(RDF.type, mer.Dump)),
        "sorry-bearing": sum(1 for _ in g.subjects(mer.hasSorry, rdflib.Literal(True))),
    }


def conformance_check(g: rdflib.Graph, mer: rdflib.Namespace, max_orphans: int) -> int:
    """Every object of mer:directlyDependsOn / mer:usesAxiom / mer:inModule
    should be present as a subject (i.e. typed) in the graph. Reports orphans."""
    print()
    print("==> ontology conformance check (dangling dep targets)")
    typed = set(g.subjects(RDF.type, None))
    failures = 0
    for prop_name in ("directlyDependsOn", "usesAxiom", "inModule"):
        prop = mer[prop_name]
        targets = set(g.objects(predicate=prop))
        orphans = [t for t in targets if t not in typed]
        if orphans:
            failures += 1
            sample = ", ".join(str(o) for o in sorted(map(str, orphans))[:max_orphans])
            print(f"    [WARN] {prop_name}: {len(orphans):,} of {len(targets):,} "
                  f"targets are not typed in this dump")
            print(f"        sample: {sample}")
        else:
            print(f"    [OK]   {prop_name}: all {len(targets):,} targets are typed")
    if failures:
        print(f"    note: orphan dep targets are common in module-local dumps; "
              f"a full env dump should have zero (or near-zero).")
    return failures


def run_queries(g: rdflib.Graph, sparql_dir: Path) -> int:
    print()
    print("==> running SPARQL queries")
    sparqls = sorted(sparql_dir.glob("*.sparql"))
    if not sparqls:
        print(f"    no .sparql files in {sparql_dir}", file=sys.stderr)
        return 1
    failures = 0
    for q in sparqls:
        text = q.read_text()
        t0 = time.monotonic()
        try:
            results = list(g.query(text))
        except Exception as e:
            print(f"    [FAIL] {q.name}: {e}")
            failures += 1
            continue
        dt = time.monotonic() - t0
        first_row = results[0] if results else None
        first_repr = (
            ", ".join(str(c) for c in first_row)
            if first_row is not None
            else "<no rows>"
        )
        if len(first_repr) > 110:
            first_repr = first_repr[:107] + "..."
        print(f"    [{len(results):>6} rows in {dt:5.2f}s] {q.name}")
        print(f"        first: {first_repr}")
    return failures


def run_shacl(dump: Path, repo: Path) -> int:
    print()
    print("==> SHACL validation (pyshacl)")
    try:
        from pyshacl import validate  # type: ignore
    except ImportError:
        print("    [FAIL] pyshacl not available; rerun with --with pyshacl")
        return 1
    shapes = repo / "Ontology" / "meridian-shapes.ttl"
    onto = repo / "Ontology" / "meridian.ttl"
    t0 = time.monotonic()
    conforms, _, report = validate(
        str(dump),
        shacl_graph=str(shapes),
        ont_graph=str(onto),
        inference="rdfs",
        debug=False,
    )
    dt = time.monotonic() - t0
    print(f"    validated in {dt:.1f}s; conforms={conforms}")
    if not conforms:
        # Truncate so the report does not flood the terminal.
        for line in report.splitlines()[:40]:
            print(f"      {line}")
        return 1
    return 0


def main() -> int:
    args = parse_args()
    if not args.dump.is_file():
        print(f"error: dump not found: {args.dump}", file=sys.stderr)
        return 2

    repo = Path(__file__).resolve().parent.parent
    sparql_dir = repo / "examples" / "sparql"
    ontology = repo / "Ontology" / "meridian.ttl"

    mer = rdflib.Namespace("https://meridian.sotofranco.dev/ontology#")

    g = load_graph(args.dump, ontology)

    print()
    print("==> declaration class counts")
    for k, v in class_counts(g, mer).items():
        print(f"    {k:14s} {v:>10,}")

    failures = 0
    failures += conformance_check(g, mer, args.max_orphans)
    if not args.no_queries:
        failures += run_queries(g, sparql_dir)
    if args.shacl:
        failures += run_shacl(args.dump, repo)

    print()
    if failures:
        print(f"==> {failures} check(s) reported issues")
        return 1
    print("==> all checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
